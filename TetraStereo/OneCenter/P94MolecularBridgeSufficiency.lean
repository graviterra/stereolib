import TetraStereo.OneCenter.P94MolecularLonePairEvidence

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP94.P94MolecularBridgeSufficiency

open CoordinateTwistInOut
open P94MolecularBicyclicFramework
open P94MolecularLonePair

/-!
# Source-operational bridge sufficiency for P-94 in/out isomerism

P-94.3.2.6 does not state a numeric bridge length.  Its criterion is operational: the bridges are
long enough when they allow the bridgehead exocyclic bond or lone pair to point either inside or
outside.  Encoding an atom-count cutoff would therefore add a rule absent from the source.

This module formalizes the stated capability directly.  Starting from all in/out premises except
bridge sufficiency, a bridge allows both directions exactly when two validated coordinate
observations of the same framework, bridgehead, and participant witness inward and outward.  The
resulting predicate fills `BridgeLongEnough`; the direction judgment itself is definitionally
unchanged because it never consults that field.  Thus the two opposite observations already
required for an in/out pair automatically discharge bridge sufficiency without circularity.
-/

/-! ## Premises with the bridge field removed -/

structure InOutPremisesWithoutBridge (Framework : Type*) where
  BicyclicFramework : RawMolecule → P94ConformationUnit → Framework → Prop
  InteriorWitness : RawMolecule → P94ConformationUnit → Framework →
    ℕ → SpatialConfiguration → CartesianPoint3 → Prop
  AtomInFramework : RawMolecule → P94ConformationUnit → Framework → ℕ → Prop
  BridgeheadInFramework : RawMolecule → P94ConformationUnit → Framework → ℕ → Prop
  LonePairAt : RawMolecule → ℕ → Prop

/-- A bridge-irrelevant premises record used only to evaluate one direction. -/
def directionPremises {Framework : Type*}
    (base : InOutPremisesWithoutBridge Framework) :
    IndependentInOutPremises Framework :=
  { BicyclicFramework := base.BicyclicFramework
    BridgeLongEnough := fun _molecule _unit _framework => True
    InteriorWitness := base.InteriorWitness
    AtomInFramework := base.AtomInFramework
    BridgeheadInFramework := base.BridgeheadInFramework
    LonePairAt := base.LonePairAt }

abbrev DirectionJudgment {Framework : Type*}
    (base : InOutPremisesWithoutBridge Framework) (molecule : RawMolecule)
    (unit : P94ConformationUnit) (observation : CoordinateInOutObservation Framework)
    (direction : BridgeheadDirection) : Prop :=
  CoordinateInOutDirectionJudgment
    (directionPremises base) molecule unit observation direction

/-! ## The exact operational criterion -/

/-- A framework's bridges are sufficient exactly when the same directed bridgehead site has
validated inward and outward coordinate realizations. -/
def BridgeAllowsBothDirections {Framework : Type*}
    (base : InOutPremisesWithoutBridge Framework) (molecule : RawMolecule)
    (unit : P94ConformationUnit) (framework : Framework) : Prop :=
  ∃ inwardObservation outwardObservation : CoordinateInOutObservation Framework,
    inwardObservation.framework = framework ∧
    outwardObservation.framework = framework ∧
    inwardObservation.bridgehead = outwardObservation.bridgehead ∧
    inwardObservation.directedParticipant = outwardObservation.directedParticipant ∧
    DirectionJudgment base molecule unit inwardObservation .inward ∧
    DirectionJudgment base molecule unit outwardObservation .outward

theorem bridgeAllowsBothDirections_iff {Framework : Type*}
    (base : InOutPremisesWithoutBridge Framework) (molecule : RawMolecule)
    (unit : P94ConformationUnit) (framework : Framework) :
    BridgeAllowsBothDirections base molecule unit framework ↔
      ∃ inwardObservation outwardObservation : CoordinateInOutObservation Framework,
        inwardObservation.framework = framework ∧
        outwardObservation.framework = framework ∧
        inwardObservation.bridgehead = outwardObservation.bridgehead ∧
        inwardObservation.directedParticipant = outwardObservation.directedParticipant ∧
        DirectionJudgment base molecule unit inwardObservation .inward ∧
        DirectionJudgment base molecule unit outwardObservation .outward :=
  Iff.rfl

/-- Restore the independent premise interface using the source-operational capability relation. -/
def bridgeDerivedPremises {Framework : Type*}
    (base : InOutPremisesWithoutBridge Framework) :
    IndependentInOutPremises Framework :=
  { BicyclicFramework := base.BicyclicFramework
    BridgeLongEnough := BridgeAllowsBothDirections base
    InteriorWitness := base.InteriorWitness
    AtomInFramework := base.AtomInFramework
    BridgeheadInFramework := base.BridgeheadInFramework
    LonePairAt := base.LonePairAt }

/-- Replacing the bridge field cannot alter a single-observation direction judgment. -/
theorem directionJudgment_bridgeDerived_iff {Framework : Type*}
    (base : InOutPremisesWithoutBridge Framework) (molecule : RawMolecule)
    (unit : P94ConformationUnit) (observation : CoordinateInOutObservation Framework)
    (direction : BridgeheadDirection) :
    CoordinateInOutDirectionJudgment (bridgeDerivedPremises base)
        molecule unit observation direction ↔
      DirectionJudgment base molecule unit observation direction :=
  Iff.rfl

theorem bridgeDerivedPremises_bridgeLongEnough_iff {Framework : Type*}
    (base : InOutPremisesWithoutBridge Framework) (molecule : RawMolecule)
    (unit : P94ConformationUnit) (framework : Framework) :
    (bridgeDerivedPremises base).BridgeLongEnough molecule unit framework ↔
      BridgeAllowsBothDirections base molecule unit framework :=
  Iff.rfl

/-- The opposite same-site observations already required by the in/out judgment construct the
source's bridge-sufficiency witness automatically. -/
theorem oppositeDirections_establish_bridgeSufficiency {Framework : Type*}
    (base : InOutPremisesWithoutBridge Framework) (molecule : RawMolecule)
    (unit : P94ConformationUnit)
    (first second : CoordinateInOutObservation Framework)
    (firstDirection secondDirection : BridgeheadDirection)
    (sameFramework : first.framework = second.framework)
    (sameBridgehead : first.bridgehead = second.bridgehead)
    (sameParticipant : first.directedParticipant = second.directedParticipant)
    (firstJudged : CoordinateInOutDirectionJudgment (bridgeDerivedPremises base)
      molecule unit first firstDirection)
    (secondJudged : CoordinateInOutDirectionJudgment (bridgeDerivedPremises base)
      molecule unit second secondDirection)
    (opposite : firstDirection ≠ secondDirection) :
    (bridgeDerivedPremises base).BridgeLongEnough molecule unit first.framework := by
  have firstBase :=
    (directionJudgment_bridgeDerived_iff
      base molecule unit first firstDirection).mp firstJudged
  have secondBase :=
    (directionJudgment_bridgeDerived_iff
      base molecule unit second secondDirection).mp secondJudged
  cases firstDirection <;> cases secondDirection
  · exact False.elim (opposite rfl)
  · exact ⟨first, second, rfl, sameFramework.symm,
      sameBridgehead, sameParticipant, firstBase, secondBase⟩
  · exact ⟨second, first, sameFramework.symm, rfl,
      sameBridgehead.symm, sameParticipant.symm, secondBase, firstBase⟩
  · exact False.elim (opposite rfl)

/-! ## Graph/electronic composition with only the interior left independent -/

structure RetainedInteriorPremises where
  InteriorWitness : RawMolecule → P94ConformationUnit → ThetaFramework →
    ℕ → SpatialConfiguration → CartesianPoint3 → Prop

def graphElectronicBasePremises (molecule : RawMolecule)
    (ledger : CertifiedLonePairLedger molecule)
    (retained : RetainedInteriorPremises) :
    InOutPremisesWithoutBridge ThetaFramework :=
  { BicyclicFramework := fun candidate unit framework => framework.ValidFor candidate unit
    InteriorWitness := retained.InteriorWitness
    AtomInFramework := fun _candidate _unit framework atom => framework.ContainsAtom atom
    BridgeheadInFramework := fun candidate unit framework atom =>
      framework.ValidFor candidate unit ∧ framework.IsBridgehead atom
    LonePairAt := fun candidate atom =>
      candidate = molecule ∧ ledger.HasLonePairAt atom }

/-- Complete represented premise adapter: theta topology and atom membership come from the raw
graph, lone pairs come from the molecule-linked electronic ledger, and bridge sufficiency is the
two-direction coordinate capability.  Only the cage-interior witness remains independent. -/
def graphElectronicBridgePremises (molecule : RawMolecule)
    (ledger : CertifiedLonePairLedger molecule)
    (retained : RetainedInteriorPremises) :
    IndependentInOutPremises ThetaFramework :=
  bridgeDerivedPremises (graphElectronicBasePremises molecule ledger retained)

theorem graphElectronicBridgePremises_bicyclicFramework_iff
    (molecule : RawMolecule) (ledger : CertifiedLonePairLedger molecule)
    (retained : RetainedInteriorPremises) (candidate : RawMolecule)
    (unit : P94ConformationUnit) (framework : ThetaFramework) :
    (graphElectronicBridgePremises molecule ledger retained).BicyclicFramework
        candidate unit framework ↔
      framework.ValidFor candidate unit :=
  Iff.rfl

theorem graphElectronicBridgePremises_atomInFramework_iff
    (molecule : RawMolecule) (ledger : CertifiedLonePairLedger molecule)
    (retained : RetainedInteriorPremises) (candidate : RawMolecule)
    (unit : P94ConformationUnit) (framework : ThetaFramework) (atom : ℕ) :
    (graphElectronicBridgePremises molecule ledger retained).AtomInFramework
        candidate unit framework atom ↔
      ∃ path ∈ framework.bridges, atom ∈ path :=
  Iff.rfl

theorem graphElectronicBridgePremises_bridgeheadInFramework_iff
    (molecule : RawMolecule) (ledger : CertifiedLonePairLedger molecule)
    (retained : RetainedInteriorPremises) (candidate : RawMolecule)
    (unit : P94ConformationUnit) (framework : ThetaFramework) (atom : ℕ) :
    (graphElectronicBridgePremises molecule ledger retained).BridgeheadInFramework
        candidate unit framework atom ↔
      framework.ValidFor candidate unit ∧ framework.IsBridgehead atom :=
  Iff.rfl

theorem graphElectronicBridgePremises_lonePairAt_iff
    (molecule : RawMolecule) (ledger : CertifiedLonePairLedger molecule)
    (retained : RetainedInteriorPremises) (candidate : RawMolecule) (atom : ℕ) :
    (graphElectronicBridgePremises molecule ledger retained).LonePairAt candidate atom ↔
      candidate = molecule ∧ ledger.HasLonePairAt atom :=
  Iff.rfl

end BlueBookP94.P94MolecularBridgeSufficiency
end TetraStereo.OneCenter
