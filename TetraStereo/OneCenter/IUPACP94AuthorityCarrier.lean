import TetraStereo.OneCenter.IUPACProvisionSemantics
import TetraStereo.OneCenter.CIPP94ConformationCompletePipeline
import TetraStereo.OneCenter.P94MolecularBridgeSufficiency

set_option autoImplicit false

/-!
# Typed authority carrier for all twelve P-94 provisions

The authority boundary reuses the independent P-94 relations and molecule-local evidence from
`CIPP94ConformationCompletePipeline`.  A policy may certify only that an evidence record was
observed for the authoritative input; it does not receive the claimed provision or descriptor.
Consequently provenance cannot act as a descriptor oracle: every claim must still match the
evidence constructor and satisfy `P94ConformationEvidence.Supports`.
-/

namespace TetraStereo.OneCenter

open BlueBookP94
open IUPACNormativeProvision
open BlueBookP94.CoordinateTwistInOut
open BlueBookP94.P94MolecularBicyclicFramework
open BlueBookP94.P94MolecularBridgeSufficiency

abbrev P94ReviewedEvidence := P94ConformationEvidence Nat ThetaFramework
abbrev P94InOutCoordinateObservation := CoordinateInOutObservation ThetaFramework

/-- Exact P-94 claims, retaining the source distinctions that share an output descriptor. -/
inductive P94AuthorityClaim where
  | conformationDefinition
  | torsionSense (sense : RotationSense)
  | torsionClass (classification : ConformationalClass)
  | torsionElectronicProxy (classification : ConformationalClass)
  | eclipsed
  | staggered
  | gauche
  | trigonalBisecting
  | trigonalEclipsing
  | sCis
  | sTrans
  | envelope
  | chair
  | boat
  | sixRingTwist
  | carbohydrateFiveRingTwist
  | halfChair
  | crown
  | tub
  | inOut
  deriving DecidableEq, Repr

namespace P94AuthorityClaim

/-- Exact manifest row owned by each source-level claim. -/
def provision : P94AuthorityClaim → IUPACNormativeProvision
  | .conformationDefinition => .p94ConformationDefinition
  | .torsionSense _ | .torsionClass _ => .p94TorsionAngle
  | .torsionElectronicProxy _ => .p94TorsionLonePairs
  | .eclipsed | .staggered | .gauche => .p94EclipsedStaggeredGauche
  | .trigonalBisecting | .trigonalEclipsing => .p94TrigonalConformations
  | .sCis | .sTrans => .p94SCisSTrans
  | .envelope => .p94Envelope
  | .chair | .boat | .sixRingTwist | .carbohydrateFiveRingTwist =>
      .p94ChairBoatTwist
  | .halfChair => .p94HalfChair
  | .crown => .p94Crown
  | .tub => .p94Tub
  | .inOut => .p94InOut

/-- Descriptor relation tested after the claim has been matched to its typed evidence. -/
def descriptor : P94AuthorityClaim → P94ConformationDescriptor
  | .conformationDefinition => .conformerPair
  | .torsionSense sense => .torsionSense sense
  | .torsionClass classification | .torsionElectronicProxy classification =>
      .torsionClass classification
  | .eclipsed => .eclipsed
  | .staggered => .staggered
  | .gauche => .torsionClass .synclinal
  | .trigonalBisecting => .bisecting
  | .trigonalEclipsing => .eclipsing
  | .sCis => .sCis
  | .sTrans => .sTrans
  | .envelope => .envelope
  | .chair => .chair
  | .boat => .boat
  | .sixRingTwist | .carbohydrateFiveRingTwist => .twist
  | .halfChair => .halfChair
  | .crown => .crown
  | .tub => .tub
  | .inOut => .inOut

def IsElectronicProxy : TorsionParticipant Nat → Prop
  | .atom _ => False
  | .lonePair _ | .duplicateAtom _ => True

/-- P-94.2.2 requires the lone-pair phantom or multiple-bond duplicate to be one of the two
participants actually selected into the torsion frame.  Merely listing an unused proxy among the
candidates cannot reroute an ordinary torsion observation to P-94.2.2. -/
def TorsionSelectsElectronicProxy (record : P94TorsionEvidence) : Prop :=
  IsElectronicProxy record.selectedFront.participant ∨
    IsElectronicProxy record.selectedRear.participant

/-- Constructor-level guard preventing a valid descriptor from being reassigned to an unrelated
P-94 provision.  The carbohydrate-specific twist branch remains explicitly distinct. -/
def MatchesEvidence : P94AuthorityClaim → P94ReviewedEvidence → Prop
  | .conformationDefinition, .conformer _ => True
  | .torsionSense _, .torsion record => record.SelectedBySourceCriteria
  | .torsionClass _, .torsion _ => True
  | .torsionElectronicProxy _, .torsion record =>
      record.SelectedBySourceCriteria ∧ TorsionSelectsElectronicProxy record
  | .eclipsed, .eclipsedStaggered _ => True
  | .staggered, .eclipsedStaggered _ => True
  | .gauche, .torsion _ => True
  | .trigonalBisecting, .trigonal _ => True
  | .trigonalEclipsing, .trigonal _ => True
  | .sCis, .conjugated _ => True
  | .sTrans, .conjugated _ => True
  | .envelope, .ringPlane _ => True
  | .chair, .ringPlane _ => True
  | .boat, .ringPlane _ => True
  | .sixRingTwist, .twist _ => True
  | .carbohydrateFiveRingTwist, .ringPlane record => record.carbohydrateFiveRing
  | .halfChair, .halfChair _ => True
  | .crown, .ringPlane _ => True
  | .tub, .ringPlane _ => True
  | .inOut, .inOut _ => True
  | _, _ => False

end P94AuthorityClaim

/-- The sole policy-controlled boundary is provenance.  Since the claim is not an argument, this
field cannot select a provision or make a descriptor true. -/
structure P94AuthorityPolicy where
  EvidenceObserved :
    AuthoritativeChemicalInput → RawMolecule →
      P94ReviewedEvidence → Prop
  /-- Provenance of the two coordinate realizations.  This field sees neither the P-94 claim nor
  either requested direction; directions are derived below from exact rational geometry. -/
  InOutCoordinatePairObserved :
    AuthoritativeChemicalInput → RawMolecule →
      P94InOutCoordinateObservation → P94InOutCoordinateObservation → Prop
  /-- Source-sensitive cage interior, indexed by the exact theta framework and bridgehead. -/
  InOutInteriorWitness :
    AuthoritativeChemicalInput → RawMolecule → P94ConformationUnit →
      ThetaFramework → Nat → SpatialConfiguration → CartesianPoint3 → Prop
  /-- Molecule-bound electronic provenance for the lone-pair branch. -/
  LonePairObserved : AuthoritativeChemicalInput → RawMolecule → Nat → Prop

def P94AuthorityPolicy.inOutBasePremises
    (policy : P94AuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (molecule : RawMolecule) : InOutPremisesWithoutBridge ThetaFramework where
  BicyclicFramework := fun candidate unit framework =>
    candidate = molecule ∧ framework.ValidFor candidate unit
  InteriorWitness := fun candidate unit framework bridgehead spatial interior =>
    candidate = molecule ∧
      policy.InOutInteriorWitness source candidate unit framework
        bridgehead spatial interior
  AtomInFramework := fun candidate _unit framework atom =>
    candidate = molecule ∧ framework.ContainsAtom atom
  BridgeheadInFramework := fun candidate unit framework atom =>
    candidate = molecule ∧
      framework.ValidFor candidate unit ∧ framework.IsBridgehead atom
  LonePairAt := fun candidate atom =>
    candidate = molecule ∧ policy.LonePairObserved source candidate atom

/-- Exact molecule-bound certificate required for the in/out evidence constructor.  Theta
topology is graph-derived, directions are coordinate-derived, and bridge sufficiency is exactly
the existence of the paired opposite-direction judgments. -/
def P94ConcreteInOutCertificateValid
    (policy : P94AuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (molecule : RawMolecule)
    (record : P94InOutEvidence ThetaFramework)
    (certificate : Option
      (P94InOutCoordinateObservation × P94InOutCoordinateObservation)) : Prop :=
  ∃ firstCoordinate secondCoordinate,
    certificate = some (firstCoordinate, secondCoordinate) ∧
      policy.InOutCoordinatePairObserved source molecule firstCoordinate secondCoordinate ∧
      firstCoordinate.spatial.positions.length = molecule.atomCount ∧
      secondCoordinate.spatial.positions.length = molecule.atomCount ∧
      firstCoordinate.framework = record.first.framework ∧
      secondCoordinate.framework = record.second.framework ∧
      firstCoordinate.bridgehead = record.first.bridgehead ∧
      secondCoordinate.bridgehead = record.second.bridgehead ∧
      firstCoordinate.directedParticipant = record.first.directedParticipant ∧
      secondCoordinate.directedParticipant = record.second.directedParticipant ∧
      record.first.framework.ValidFor molecule record.unit ∧
      record.second.framework.ValidFor molecule record.unit ∧
      let base := policy.inOutBasePremises source molecule
      let premises := bridgeDerivedPremises base
      CoordinateInOutDirectionJudgment premises molecule record.unit
          firstCoordinate record.first.direction ∧
        CoordinateInOutDirectionJudgment premises molecule record.unit
          secondCoordinate record.second.direction ∧
        (record.bicyclicSystem ↔ record.first.framework.ValidFor molecule record.unit) ∧
        (record.first.bridgeLongEnough ↔
          BridgeAllowsBothDirections base molecule record.unit record.first.framework) ∧
        (record.second.bridgeLongEnough ↔
          BridgeAllowsBothDirections base molecule record.unit record.second.framework)

def P94InOutCertificateMatches
    (policy : P94AuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (molecule : RawMolecule)
    (evidence : P94ReviewedEvidence)
    (certificate : Option
      (P94InOutCoordinateObservation × P94InOutCoordinateObservation)) : Prop :=
  match evidence with
  | .inOut record =>
      P94ConcreteInOutCertificateValid policy source molecule record certificate
  | _ => certificate = none

structure P94AuthorityObservation (policy : P94AuthorityPolicy) where
  molecule : RawMolecule
  evidence : P94ReviewedEvidence
  claim : P94AuthorityClaim
  inOutCertificate? : Option
    (P94InOutCoordinateObservation × P94InOutCoordinateObservation) := none

def P94AuthorityObservation.ValidFor
    (policy : P94AuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P94AuthorityObservation policy) : Prop :=
  observation.molecule.AuthoritativeStructureAgreement source ∧
    policy.EvidenceObserved source observation.molecule observation.evidence ∧
    observation.evidence.unit.ValidFor observation.molecule ∧
    observation.evidence.MolecularRolesValid observation.molecule ∧
    observation.claim.MatchesEvidence observation.evidence ∧
    observation.evidence.Supports observation.claim.descriptor ∧
    P94InOutCertificateMatches policy source observation.molecule
      observation.evidence observation.inOutCertificate?

/-- A row-specific judge is a projection from the shared authority language, not a new
applicability oracle. -/
def P94AuthorityObservation.ValidForProvision
    (policy : P94AuthorityPolicy)
    (provision : IUPACNormativeProvision)
    (source : AuthoritativeChemicalInput)
    (observation : P94AuthorityObservation policy) : Prop :=
  observation.ValidFor policy source ∧ observation.claim.provision = provision

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P94AuthorityClaim.provision
assert_kernel_only TetraStereo.OneCenter.P94AuthorityClaim.descriptor
assert_kernel_only TetraStereo.OneCenter.P94AuthorityClaim.MatchesEvidence
assert_kernel_only TetraStereo.OneCenter.P94ConcreteInOutCertificateValid
assert_kernel_only TetraStereo.OneCenter.P94InOutCertificateMatches
assert_kernel_only TetraStereo.OneCenter.P94AuthorityObservation.ValidFor
assert_kernel_only TetraStereo.OneCenter.P94AuthorityObservation.ValidForProvision
