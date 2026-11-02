import TetraStereo.OneCenter.IUPACNext54ProvisionInventory
import TetraStereo.OneCenter.IUPACPrimitive35ReviewedSemantics
import TetraStereo.OneCenter.P92StereogenicUnitSemantics

set_option autoImplicit false

/-!
# Independent reviewed targets for the 21 foundational P-92 provisions

This module compiles the complete P-92.1.1--P-92.1.3 foundational slice into one exact,
classifier-bound reviewed table.  It reuses the independent Blue Book relations and does not call
the production analyzer, promote maturity, or claim closure of the separate eleven-row digraph and
Rule-1a slice.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

structure P92StereogenicUnitAuthorityObservation where
  entity : Bool
  unit : Bool
  mirror : Bool → Bool
  superposable : Bool → Bool → Prop
  belongsTo : Bool → Bool → Prop
  localChange : Bool → Bool → Prop
  stereoisomers : Bool → Bool → Prop

def P92StereogenicUnitsJudged
    (observation : P92StereogenicUnitAuthorityObservation) : Prop :=
  BlueBookP92.IsStereogenicUnit observation.localChange observation.stereoisomers
      observation.unit ∧
    BlueBookP92.ChiralEntityHasStereogenicUnit
      (BlueBookP92.IsChiral observation.mirror observation.superposable)
      observation.belongsTo
      (BlueBookP92.IsStereogenicUnit observation.localChange observation.stereoisomers) ∧
    (BlueBookP92.IsChiral observation.mirror observation.superposable observation.entity ∨
      BlueBookP92.IsAchiral observation.mirror observation.superposable observation.entity)

def p92StereogenicUnitsReference : ProvisionReference where
  Observation := P92StereogenicUnitAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation => P92StereogenicUnitsJudged observation

inductive P92ChiralityClassification where
  | chiral
  | achiral
  deriving DecidableEq, Repr

structure P92ChiralityAuthorityObservation where
  entity : Bool
  mirror : Bool → Bool
  superposable : Bool → Bool → Prop
  classification : P92ChiralityClassification

def p92ChiralityDefinitionReference : ProvisionReference where
  Observation := P92ChiralityAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation =>
    match observation.classification with
    | .chiral =>
        BlueBookP92.IsChiral observation.mirror observation.superposable observation.entity
    | .achiral =>
        BlueBookP92.IsAchiral observation.mirror observation.superposable observation.entity

structure P92ChiralityCenterAuthorityObservation where
  observation : BlueBookP92.FourLigandCenterObservation Nat Nat
  distinguishable : Nat → Nat → Prop
  stereoisomers : Nat → Nat → Prop

def p92ChiralityCenterDefinitionReference : ProvisionReference where
  Observation := P92ChiralityCenterAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input authority =>
    BlueBookP92.IsChiralityCenter authority.distinguishable authority.stereoisomers
      authority.observation

def p92ChiralityAxisDefinitionReference : ProvisionReference where
  Observation := BlueBookP92.ChiralityAxisObservation
  Applicable := fun _input => True
  Judges := fun _input observation => BlueBookP92.IsChiralityAxis observation

def p92ChiralityPlaneDefinitionReference : ProvisionReference where
  Observation := BlueBookP92.ChiralityPlaneObservation
  Applicable := fun _input => True
  Judges := fun _input observation => BlueBookP92.IsChiralityPlane observation

structure P92PseudoDescriptorBehaviour where
  descriptor : BlueBookP92.PseudoDescriptor
  reflectedDescriptor : BlueBookP92.PseudoDescriptor
  descriptorAfterLigandExchange : BlueBookP92.PseudoDescriptor

def PseudoDescriptorBehaviourJudged (behaviour : P92PseudoDescriptorBehaviour) : Prop :=
  behaviour.descriptor.reflected = behaviour.reflectedDescriptor ∧
    behaviour.reflectedDescriptor = behaviour.descriptor ∧
    behaviour.descriptor.afterLigandExchange = behaviour.descriptorAfterLigandExchange ∧
    behaviour.descriptorAfterLigandExchange ≠ behaviour.descriptor

instance (behaviour : P92PseudoDescriptorBehaviour) :
    Decidable (PseudoDescriptorBehaviourJudged behaviour) := by
  unfold PseudoDescriptorBehaviourJudged
  infer_instance

structure P92PseudoasymmetricCenterAuthorityObservation where
  ligand : Fin 4 → Nat
  distinguishable : Nat → Nat → Prop
  enantiomorphic : Nat → Nat → Prop
  behaviour : P92PseudoDescriptorBehaviour

structure P92PseudoasymmetricAxisAuthorityObservation where
  nearEndLigand : Fin 2 → Nat
  farEndLigand : Fin 2 → Nat
  ligand : Fin 4 → Nat
  endPairsCoverLigands :
    List.ofFn nearEndLigand ++ List.ofFn farEndLigand = List.ofFn ligand
  distinguishable : Nat → Nat → Prop
  enantiomorphic : Nat → Nat → Prop
  behaviour : P92PseudoDescriptorBehaviour

structure P92PseudoasymmetricPlaneAuthorityObservation where
  inPlaneReferenceLigand : Fin 2 → Nat
  outOfPlaneLigand : Fin 2 → Nat
  ligand : Fin 4 → Nat
  planeGroupsCoverLigands :
    List.ofFn inPlaneReferenceLigand ++ List.ofFn outOfPlaneLigand = List.ofFn ligand
  distinguishable : Nat → Nat → Prop
  enantiomorphic : Nat → Nat → Prop
  behaviour : P92PseudoDescriptorBehaviour

inductive P92PseudoasymmetricUnitAuthorityObservation where
  | center (observation : P92PseudoasymmetricCenterAuthorityObservation)
  | axis (observation : P92PseudoasymmetricAxisAuthorityObservation)
  | plane (observation : P92PseudoasymmetricPlaneAuthorityObservation)

def p92PseudoasymmetricUnitDefinitionReference : ProvisionReference where
  Observation := P92PseudoasymmetricUnitAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation =>
    match observation with
    | .center center =>
        BlueBookP92.IsPseudoasymmetricUnit center.ligand center.distinguishable
            center.enantiomorphic ∧
          PseudoDescriptorBehaviourJudged center.behaviour
    | .axis axis =>
        BlueBookP92.IsPseudoasymmetricUnit axis.ligand axis.distinguishable
            axis.enantiomorphic ∧
          PseudoDescriptorBehaviourJudged axis.behaviour
    | .plane plane =>
        BlueBookP92.IsPseudoasymmetricUnit plane.ligand plane.distinguishable
            plane.enantiomorphic ∧
          PseudoDescriptorBehaviourJudged plane.behaviour

def p92CisTransDoubleBondUnitDefinitionReference : ProvisionReference where
  Observation := BlueBookP92.DoubleBondUnitObservation
  Applicable := fun _input => True
  Judges := fun _input observation => BlueBookP92.IsCisTransDoubleBondUnit observation

def p92EnantiomorphicDoubleBondUnitDefinitionReference : ProvisionReference where
  Observation := BlueBookP92.EnantiomorphicDoubleBondObservation
  Applicable := fun _input => True
  Judges := fun _input observation => BlueBookP92.IsEnantiomorphicDoubleBond observation

def p92BondingNumberScopeReference : ProvisionReference where
  Observation := Nat
  Applicable := fun _input => True
  Judges := fun _input bondingNumber => BlueBookP92.WithinBondingNumberScope bondingNumber

structure P92FinitePriorityGeometryFrame where
  priorities : List Nat

def P92FinitePriorityGeometryFrame.priorityAt
    (frame : P92FinitePriorityGeometryFrame) (position : Nat) : Nat :=
  frame.priorities[position]?.getD 0

inductive P92OrientedPriorityPath where
  | clockwise (donorPositions : List Nat)
  | anticlockwise (donorPositions : List Nat)

def P92OrientedPriorityPath.donorPositions : P92OrientedPriorityPath → List Nat
  | .clockwise positions | .anticlockwise positions => positions

def P92OrientedPriorityPath.sense : P92OrientedPriorityPath → BlueBookP92.TurnSense
  | .clockwise _ => .clockwise
  | .anticlockwise _ => .anticlockwise

def PriorityPathBackedByFrame
    (frame : P92FinitePriorityGeometryFrame) (path : P92OrientedPriorityPath) : Prop :=
  path.donorPositions.Nodup ∧
    ∀ position ∈ path.donorPositions, position < frame.priorities.length

def StrictPriorityProgression
    (frame : P92FinitePriorityGeometryFrame) (path : P92OrientedPriorityPath) : Prop :=
  PriorityPathBackedByFrame frame path ∧
    (path.donorPositions.map frame.priorityAt).Pairwise fun senior junior => senior < junior

structure P92CenterChiralityRuleAuthorityObservation where
  frame : P92FinitePriorityGeometryFrame
  priorityPath : P92OrientedPriorityPath
  leastPriorityPosition : Nat
  pseudoasymmetric : Bool
  viewedFromSideRemoteFromLowestPriority : Prop
  descriptor : BlueBookP92.CenterDescriptor

def p92CenterChiralityRuleReference : ProvisionReference where
  Observation := P92CenterChiralityRuleAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation =>
    observation.frame.priorities.length = 4 ∧
      observation.frame.priorities.Nodup ∧
      (∀ priority ∈ observation.frame.priorities, 0 < priority) ∧
      observation.priorityPath.donorPositions.length = 3 ∧
      StrictPriorityProgression observation.frame observation.priorityPath ∧
      observation.leastPriorityPosition < observation.frame.priorities.length ∧
      observation.leastPriorityPosition ∉ observation.priorityPath.donorPositions ∧
      (∀ position ∈ observation.priorityPath.donorPositions,
        observation.frame.priorityAt position <
          observation.frame.priorityAt observation.leastPriorityPosition) ∧
      observation.viewedFromSideRemoteFromLowestPriority ∧
      BlueBookP92.centerDescriptor observation.pseudoasymmetric
        observation.priorityPath.sense =
        observation.descriptor

structure P92AxisChiralityRuleAuthorityObservation where
  frame : P92FinitePriorityGeometryFrame
  nearEndPositions : List Nat
  farEndPositions : List Nat
  nearSeniorPosition : Nat
  nearJuniorPosition : Nat
  farSeniorPosition : Nat
  farJuniorPosition : Nat
  priorityPath : P92OrientedPriorityPath
  viewedFromNearSeniorTowardFarJunior : Prop
  descriptor : BlueBookP92.AxialDescriptor

def P92AxisChiralityRuleJudged
    (observation : P92AxisChiralityRuleAuthorityObservation) : Prop :=
  observation.frame.priorities.length = 4 ∧
    (∀ priority ∈ observation.frame.priorities, 0 < priority) ∧
    observation.nearEndPositions.length = 2 ∧
    observation.farEndPositions.length = 2 ∧
    (observation.nearEndPositions ++ observation.farEndPositions).Nodup ∧
    (∀ position ∈ observation.nearEndPositions ++ observation.farEndPositions,
      position < observation.frame.priorities.length) ∧
    observation.nearSeniorPosition ∈ observation.nearEndPositions ∧
    observation.nearJuniorPosition ∈ observation.nearEndPositions ∧
    observation.farSeniorPosition ∈ observation.farEndPositions ∧
    observation.farJuniorPosition ∈ observation.farEndPositions ∧
    observation.frame.priorityAt observation.nearSeniorPosition <
      observation.frame.priorityAt observation.nearJuniorPosition ∧
    observation.frame.priorityAt observation.farSeniorPosition <
      observation.frame.priorityAt observation.farJuniorPosition ∧
    observation.priorityPath.donorPositions =
      [observation.nearSeniorPosition, observation.nearJuniorPosition,
        observation.farSeniorPosition] ∧
    PriorityPathBackedByFrame observation.frame observation.priorityPath ∧
    observation.viewedFromNearSeniorTowardFarJunior ∧
    BlueBookP92.axialDescriptor observation.priorityPath.sense = observation.descriptor

def p92AxisChiralityRuleReference : ProvisionReference where
  Observation := P92AxisChiralityRuleAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation => P92AxisChiralityRuleJudged observation

structure P92PlaneChiralityRuleAuthorityObservation where
  frame : P92FinitePriorityGeometryFrame
  derivedPriorityPath : P92OrientedPriorityPath
  leastPriorityPosition : Nat
  derivedTetrahedronConstructed : Prop
  descriptor : BlueBookP92.PlanarDescriptor

def P92PlaneChiralityRuleJudged
    (observation : P92PlaneChiralityRuleAuthorityObservation) : Prop :=
  observation.frame.priorities.length = 4 ∧
    observation.frame.priorities.Nodup ∧
    observation.derivedPriorityPath.donorPositions.length = 3 ∧
    StrictPriorityProgression observation.frame observation.derivedPriorityPath ∧
    observation.leastPriorityPosition < observation.frame.priorities.length ∧
    observation.leastPriorityPosition ∉ observation.derivedPriorityPath.donorPositions ∧
    (∀ position ∈ observation.derivedPriorityPath.donorPositions,
      observation.frame.priorityAt position <
        observation.frame.priorityAt observation.leastPriorityPosition) ∧
    observation.derivedTetrahedronConstructed ∧
    BlueBookP92.planarDescriptor observation.derivedPriorityPath.sense =
      observation.descriptor

def p92PlaneChiralityRuleReference : ProvisionReference where
  Observation := P92PlaneChiralityRuleAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation => P92PlaneChiralityRuleJudged observation

inductive P92ChiralityRuleGeneralAuthorityObservation where
  | center (observation : P92CenterChiralityRuleAuthorityObservation)
  | axis (observation : P92AxisChiralityRuleAuthorityObservation)
  | plane (observation : P92PlaneChiralityRuleAuthorityObservation)

def p92ChiralityRuleGeneralReference : ProvisionReference where
  Observation := P92ChiralityRuleGeneralAuthorityObservation
  Applicable := fun _input => True
  Judges := fun input observation =>
    match observation with
    | .center center => p92CenterChiralityRuleReference.Judges input center
    | .axis axis => p92AxisChiralityRuleReference.Judges input axis
    | .plane plane => p92PlaneChiralityRuleReference.Judges input plane

inductive P92HelicalEntityKind where
  | helix
  | propeller
  | screw
  deriving DecidableEq, Repr

/-- A handed helical path is geometry evidence: handedness is read from the constructor, while the
positions record the ordered reference groups that generated it. -/
inductive P92OrientedHelicalPath where
  | leftHanded (referencePositions : List Nat)
  | rightHanded (referencePositions : List Nat)

def P92OrientedHelicalPath.referencePositions : P92OrientedHelicalPath → List Nat
  | .leftHanded positions | .rightHanded positions => positions

def P92OrientedHelicalPath.handedness :
    P92OrientedHelicalPath → BlueBookP92.HelixHandedness
  | .leftHanded _ => .leftHanded
  | .rightHanded _ => .rightHanded

structure P92HelicityRuleAuthorityObservation where
  entityKind : P92HelicalEntityKind
  referenceGroups : List Nat
  orientedPath : P92OrientedHelicalPath
  descriptor : BlueBookP92.Helicity

def P92HelicityRuleJudged (observation : P92HelicityRuleAuthorityObservation) : Prop :=
  3 ≤ observation.referenceGroups.length ∧
    observation.referenceGroups.Nodup ∧
    observation.orientedPath.referencePositions =
      List.range observation.referenceGroups.length ∧
    BlueBookP92.helicityDescriptor observation.orientedPath.handedness =
      observation.descriptor

instance (observation : P92HelicityRuleAuthorityObservation) :
    Decidable (P92HelicityRuleJudged observation) := by
  unfold P92HelicityRuleJudged
  infer_instance

def p92HelicityRuleReference : ProvisionReference where
  Observation := P92HelicityRuleAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation => P92HelicityRuleJudged observation

structure P92HelicityAxisAuthorityObservation where
  frame : P92FinitePriorityGeometryFrame
  nearEndPositions : List Nat
  farEndPositions : List Nat
  nearSeniorPosition : Nat
  farSeniorPosition : Nat
  orientedPath : P92OrientedPriorityPath
  viewedAlongAxisFromNearToFar : Prop
  descriptor : BlueBookP92.Helicity

def P92HelicityAxisJudged (observation : P92HelicityAxisAuthorityObservation) : Prop :=
  observation.frame.priorities.length = 4 ∧
    (∀ priority ∈ observation.frame.priorities, 0 < priority) ∧
    observation.nearEndPositions.length = 2 ∧
    observation.farEndPositions.length = 2 ∧
    (observation.nearEndPositions ++ observation.farEndPositions).Nodup ∧
    (∀ position ∈ observation.nearEndPositions ++ observation.farEndPositions,
      position < observation.frame.priorities.length) ∧
    observation.nearSeniorPosition ∈ observation.nearEndPositions ∧
    observation.farSeniorPosition ∈ observation.farEndPositions ∧
    (∀ other ∈ observation.nearEndPositions,
      other ≠ observation.nearSeniorPosition →
        observation.frame.priorityAt observation.nearSeniorPosition <
          observation.frame.priorityAt other) ∧
    (∀ other ∈ observation.farEndPositions,
      other ≠ observation.farSeniorPosition →
        observation.frame.priorityAt observation.farSeniorPosition <
          observation.frame.priorityAt other) ∧
    observation.orientedPath.donorPositions =
      [observation.nearSeniorPosition, observation.farSeniorPosition] ∧
    PriorityPathBackedByFrame observation.frame observation.orientedPath ∧
    observation.viewedAlongAxisFromNearToFar ∧
    BlueBookP92.axialHelicityDescriptor observation.orientedPath.sense =
      observation.descriptor

def p92HelicityAxisReference : ProvisionReference where
  Observation := P92HelicityAxisAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation => P92HelicityAxisJudged observation

inductive P92PlanarTorsionConstruction where
  | negative (firstInPlane secondInPlane attachedReference : Nat)
  | zero (firstInPlane secondInPlane attachedReference : Nat)
  | positive (firstInPlane secondInPlane attachedReference : Nat)

def P92PlanarTorsionConstruction.firstInPlane : P92PlanarTorsionConstruction → Nat
  | .negative first _ _ | .zero first _ _ | .positive first _ _ => first

def P92PlanarTorsionConstruction.secondInPlane : P92PlanarTorsionConstruction → Nat
  | .negative _ second _ | .zero _ second _ | .positive _ second _ => second

def P92PlanarTorsionConstruction.attachedReference : P92PlanarTorsionConstruction → Nat
  | .negative _ _ attached | .zero _ _ attached | .positive _ _ attached => attached

def P92PlanarTorsionConstruction.signedTorsion :
    P92PlanarTorsionConstruction → BlueBookP92.SignedTorsion
  | .negative _ _ _ => .negative
  | .zero _ _ _ => .zero
  | .positive _ _ _ => .positive

structure P92HelicityPlaneAuthorityObservation where
  frame : P92FinitePriorityGeometryFrame
  referencePlanePositions : List Nat
  torsionConstruction : P92PlanarTorsionConstruction
  descriptor : Option BlueBookP92.Helicity

def P92HelicityPlaneJudged (observation : P92HelicityPlaneAuthorityObservation) : Prop :=
  observation.frame.priorities.Nodup ∧
    observation.referencePlanePositions.Nodup ∧
    2 ≤ observation.referencePlanePositions.length ∧
    (∀ position ∈ observation.referencePlanePositions,
      position < observation.frame.priorities.length) ∧
    observation.torsionConstruction.firstInPlane ∈
      observation.referencePlanePositions ∧
    observation.torsionConstruction.secondInPlane ∈
      observation.referencePlanePositions ∧
    observation.torsionConstruction.firstInPlane ≠
      observation.torsionConstruction.secondInPlane ∧
    observation.frame.priorityAt observation.torsionConstruction.firstInPlane <
      observation.frame.priorityAt observation.torsionConstruction.secondInPlane ∧
    observation.torsionConstruction.attachedReference <
      observation.frame.priorities.length ∧
    observation.torsionConstruction.attachedReference ∉
      observation.referencePlanePositions ∧
    BlueBookP92.planarHelicityDescriptor?
        observation.torsionConstruction.signedTorsion =
      observation.descriptor

def p92HelicityPlaneReference : ProvisionReference where
  Observation := P92HelicityPlaneAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation => P92HelicityPlaneJudged observation

structure P92RSMPDescriptorCorrespondenceAuthorityObservation where
  application : BlueBookP92.HelicityApplication
  helicity : BlueBookP92.Helicity
  descriptor : BlueBookP92.RSDescriptor

def p92RSMPDescriptorCorrespondenceReference : ProvisionReference where
  Observation := P92RSMPDescriptorCorrespondenceAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation =>
    BlueBookP92.correspondingRS observation.application observation.helicity =
      observation.descriptor

def p92SequenceRulePropertyClassesReference : ProvisionReference :=
  unaryAuthorityReference BlueBookP92.SequenceRule BlueBookP92.RulePropertyClass
    BlueBookP92.propertyClass

def p92SequenceRuleReflectionBehaviorReference : ProvisionReference :=
  unaryAuthorityReference BlueBookP92.SequenceRule BlueBookP92.ReflectionBehaviour
    BlueBookP92.reflectionBehaviour

structure P92LigandBondGraph where
  ligandAtoms : List Nat
  coreAtoms : List Nat
  bonds : List (Nat × Nat)

def P92LigandBondGraph.Bonded (graph : P92LigandBondGraph) (first second : Nat) : Prop :=
  (first, second) ∈ graph.bonds ∨ (second, first) ∈ graph.bonds

/-- A path is checked solely against the frozen bond graph; its endpoints and every adjacent edge
are explicit, so connectivity is not supplied as an opaque proposition. -/
def P92BondPath
    (graph : P92LigandBondGraph) (first last : Nat) (path : List Nat) : Prop :=
  path.Nodup ∧
    path.head? = some first ∧
    path.getLast? = some last ∧
    ∀ edge ∈ path.zip path.tail, graph.Bonded edge.1 edge.2

def P92SimpleBondCycle (graph : P92LigandBondGraph) (cycle : List Nat) : Prop :=
  3 ≤ cycle.length ∧
    cycle.Nodup ∧
    (∀ edge ∈ cycle.zip cycle.tail, graph.Bonded edge.1 edge.2) ∧
    ∃ first last,
      cycle.head? = some first ∧
        cycle.getLast? = some last ∧
        graph.Bonded last first

structure P92LigandDentateKindsAuthorityObservation where
  graph : P92LigandBondGraph
  coordinationCore : Nat
  donorAtoms : List Nat
  cyclic : Bool
  denticity : BlueBookP92.Denticity

def P92GraphDerivedDonorSet
    (graph : P92LigandBondGraph) (coordinationCore : Nat) (donorAtoms : List Nat) : Prop :=
  donorAtoms.Nodup ∧
    (∀ donor ∈ donorAtoms,
      donor ∈ graph.ligandAtoms ∧ graph.Bonded donor coordinationCore) ∧
    (∀ atom ∈ graph.ligandAtoms,
      graph.Bonded atom coordinationCore → atom ∈ donorAtoms)

def P92LigandDentateKindsJudged
    (observation : P92LigandDentateKindsAuthorityObservation) : Prop :=
  observation.graph.ligandAtoms.Nodup ∧
    observation.graph.coreAtoms.Nodup ∧
    (∀ atom ∈ observation.graph.ligandAtoms, atom ∉ observation.graph.coreAtoms) ∧
    observation.graph.bonds.Nodup ∧
    (∀ bond ∈ observation.graph.bonds,
      bond.1 ∈ observation.graph.ligandAtoms ++ observation.graph.coreAtoms ∧
        bond.2 ∈ observation.graph.ligandAtoms ++ observation.graph.coreAtoms) ∧
    observation.coordinationCore ∈ observation.graph.coreAtoms ∧
    P92GraphDerivedDonorSet observation.graph observation.coordinationCore
      observation.donorAtoms ∧
    (∀ first ∈ observation.graph.ligandAtoms,
      ∀ last ∈ observation.graph.ligandAtoms,
        ∃ path,
          P92BondPath observation.graph first last path ∧
            ∀ atom ∈ path, atom ∈ observation.graph.ligandAtoms) ∧
    (observation.cyclic = true ↔
      ∃ cycle,
        P92SimpleBondCycle observation.graph cycle ∧
          ∀ atom ∈ cycle, atom ∈ observation.graph.ligandAtoms) ∧
    match observation.denticity with
    | .monodentate => observation.donorAtoms.length = 1
    | .nDentate n _ => observation.donorAtoms.length = n

def p92LigandDentateKindsReference : ProvisionReference where
  Observation := P92LigandDentateKindsAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation => P92LigandDentateKindsJudged observation

def P92FirstStrictOrdering : List Ordering → Ordering
  | [] => .eq
  | .eq :: remaining => P92FirstStrictOrdering remaining
  | .lt :: _ => .lt
  | .gt :: _ => .gt

/-- `Fin caseCount` is the complete declared comparison domain.  Each rule either does not apply to
a case or produces its independently recorded comparison; no aggregate rule outcome is accepted. -/
structure P92SequenceRuleComparisonModel where
  caseCount : Nat
  evaluation : BlueBookP92.SequenceRule → Fin caseCount → Option Ordering

def P92SequenceRuleComparisonModel.applicableResults
    (model : P92SequenceRuleComparisonModel) (rule : BlueBookP92.SequenceRule) : List Ordering :=
  (List.ofFn fun caseIndex => model.evaluation rule caseIndex).filterMap id

def P92SequenceRuleComparisonModel.certifiedOutcome
    (model : P92SequenceRuleComparisonModel) (rule : BlueBookP92.SequenceRule) : Ordering :=
  P92FirstStrictOrdering (model.applicableResults rule)

structure P92SequenceRuleHierarchyAuthorityObservation where
  model : P92SequenceRuleComparisonModel
  decision : Option (BlueBookP92.SequenceRule × Ordering)

def P92SequenceRuleHierarchyJudged
    (observation : P92SequenceRuleHierarchyAuthorityObservation) : Prop :=
  0 < observation.model.caseCount ∧
    BlueBookP92.firstStrictDecision BlueBookP92.ruleOrder observation.model.certifiedOutcome =
      observation.decision

instance (observation : P92SequenceRuleHierarchyAuthorityObservation) :
    Decidable (P92SequenceRuleHierarchyJudged observation) := by
  unfold P92SequenceRuleHierarchyJudged
  infer_instance

def p92SequenceRuleHierarchyReference : ProvisionReference where
  Observation := P92SequenceRuleHierarchyAuthorityObservation
  Applicable := fun _input => True
  Judges := fun _input observation => P92SequenceRuleHierarchyJudged observation

def next54P92FoundationalProvisions : List IUPACNormativeProvision :=
  p92FoundationalSemanticsSlice

inductive Next54P92FoundationalAuthorityRow where
  | stereogenicUnits
  | chiralityDefinition
  | chiralityCenterDefinition
  | chiralityAxisDefinition
  | chiralityPlaneDefinition
  | pseudoasymmetricUnitDefinition
  | cisTransDoubleBondUnitDefinition
  | enantiomorphicDoubleBondUnitDefinition
  | bondingNumberScope
  | chiralityRuleGeneral
  | centerChiralityRule
  | axisChiralityRule
  | planeChiralityRule
  | helicityRule
  | helicityAxis
  | helicityPlane
  | rsmpDescriptorCorrespondence
  | sequenceRulePropertyClasses
  | sequenceRuleReflectionBehavior
  | ligandDentateKinds
  | sequenceRuleHierarchy
  deriving DecidableEq, Repr

namespace Next54P92FoundationalAuthorityRow

def all : List Next54P92FoundationalAuthorityRow :=
  [ .stereogenicUnits
  , .chiralityDefinition
  , .chiralityCenterDefinition
  , .chiralityAxisDefinition
  , .chiralityPlaneDefinition
  , .pseudoasymmetricUnitDefinition
  , .cisTransDoubleBondUnitDefinition
  , .enantiomorphicDoubleBondUnitDefinition
  , .bondingNumberScope
  , .chiralityRuleGeneral
  , .centerChiralityRule
  , .axisChiralityRule
  , .planeChiralityRule
  , .helicityRule
  , .helicityAxis
  , .helicityPlane
  , .rsmpDescriptorCorrespondence
  , .sequenceRulePropertyClasses
  , .sequenceRuleReflectionBehavior
  , .ligandDentateKinds
  , .sequenceRuleHierarchy
  ]

def provision : Next54P92FoundationalAuthorityRow → IUPACNormativeProvision
  | .stereogenicUnits => .p92StereogenicUnits
  | .chiralityDefinition => .p92ChiralityDefinition
  | .chiralityCenterDefinition => .p92ChiralityCenterDefinition
  | .chiralityAxisDefinition => .p92ChiralityAxisDefinition
  | .chiralityPlaneDefinition => .p92ChiralityPlaneDefinition
  | .pseudoasymmetricUnitDefinition => .p92PseudoasymmetricUnitDefinition
  | .cisTransDoubleBondUnitDefinition => .p92CisTransDoubleBondUnitDefinition
  | .enantiomorphicDoubleBondUnitDefinition => .p92EnantiomorphicDoubleBondUnitDefinition
  | .bondingNumberScope => .p92BondingNumberScope
  | .chiralityRuleGeneral => .p92ChiralityRuleGeneral
  | .centerChiralityRule => .p92CenterChiralityRule
  | .axisChiralityRule => .p92AxisChiralityRule
  | .planeChiralityRule => .p92PlaneChiralityRule
  | .helicityRule => .p92HelicityRule
  | .helicityAxis => .p92HelicityAxis
  | .helicityPlane => .p92HelicityPlane
  | .rsmpDescriptorCorrespondence => .p92RSMPDescriptorCorrespondence
  | .sequenceRulePropertyClasses => .p92SequenceRulePropertyClasses
  | .sequenceRuleReflectionBehavior => .p92SequenceRuleReflectionBehavior
  | .ligandDentateKinds => .p92LigandDentateKinds
  | .sequenceRuleHierarchy => .p92SequenceRuleHierarchy

def kind : Next54P92FoundationalAuthorityRow → ProvisionKind
  | .stereogenicUnits | .chiralityDefinition | .chiralityCenterDefinition |
      .chiralityAxisDefinition | .chiralityPlaneDefinition | .pseudoasymmetricUnitDefinition |
      .cisTransDoubleBondUnitDefinition | .enantiomorphicDoubleBondUnitDefinition |
      .bondingNumberScope => .perception
  | .sequenceRulePropertyClasses | .sequenceRuleReflectionBehavior | .ligandDentateKinds |
      .sequenceRuleHierarchy => .sequenceRule
  | _ => .spatialDescriptor

def reference : Next54P92FoundationalAuthorityRow → ProvisionReference
  | .stereogenicUnits => p92StereogenicUnitsReference
  | .chiralityDefinition => p92ChiralityDefinitionReference
  | .chiralityCenterDefinition => p92ChiralityCenterDefinitionReference
  | .chiralityAxisDefinition => p92ChiralityAxisDefinitionReference
  | .chiralityPlaneDefinition => p92ChiralityPlaneDefinitionReference
  | .pseudoasymmetricUnitDefinition => p92PseudoasymmetricUnitDefinitionReference
  | .cisTransDoubleBondUnitDefinition => p92CisTransDoubleBondUnitDefinitionReference
  | .enantiomorphicDoubleBondUnitDefinition => p92EnantiomorphicDoubleBondUnitDefinitionReference
  | .bondingNumberScope => p92BondingNumberScopeReference
  | .chiralityRuleGeneral => p92ChiralityRuleGeneralReference
  | .centerChiralityRule => p92CenterChiralityRuleReference
  | .axisChiralityRule => p92AxisChiralityRuleReference
  | .planeChiralityRule => p92PlaneChiralityRuleReference
  | .helicityRule => p92HelicityRuleReference
  | .helicityAxis => p92HelicityAxisReference
  | .helicityPlane => p92HelicityPlaneReference
  | .rsmpDescriptorCorrespondence => p92RSMPDescriptorCorrespondenceReference
  | .sequenceRulePropertyClasses => p92SequenceRulePropertyClassesReference
  | .sequenceRuleReflectionBehavior => p92SequenceRuleReflectionBehaviorReference
  | .ligandDentateKinds => p92LigandDentateKindsReference
  | .sequenceRuleHierarchy => p92SequenceRuleHierarchyReference

def semantics (row : Next54P92FoundationalAuthorityRow) : ReviewedProvisionSemantics where
  kind := row.kind
  sourceSuppliesRule := true
  reference := row.reference

@[simp] theorem all_length : all.length = 21 := by rfl

theorem all_nodup : all.Nodup := by decide

@[simp] theorem all_provisions_exact : all.map provision = next54P92FoundationalProvisions := by
  rfl

@[simp] theorem classifier_exact (row : Next54P92FoundationalAuthorityRow) :
    next54Kind? row.provision = some row.kind := by
  cases row <;>
    simp [next54Kind?, next54SequenceRuleProvisions, next54PerceptionProvisions,
      next54SpatialDescriptorProvisions, provision, kind]

/-! ## Abstract satisfiability of every input-invariant foundational row -/

/-- The foundational relations formalize source-level definitions and comparison models; they do
not claim that their observation is realized by the carrier molecule.  The empty input is used
only to package a structurally well-formed carrier for the global reference-satisfiability field. -/
def witnessInput : AuthoritativeChemicalInput where
  molecule := { atoms := [], interactions := [] }

@[simp] theorem witnessInput_structurallyWellFormed :
    witnessInput.StructurallyWellFormed := by
  simp [witnessInput, AuthoritativeChemicalInput.StructurallyWellFormed,
    SemanticMolecule.StructurallyWellFormed,
    AuthoritativeChemicalInput.SpatialIndicesWellFormed,
    AuthoritativeChemicalInput.DiagramIndicesWellFormed]

def stereogenicUnitsWitness : P92StereogenicUnitAuthorityObservation where
  entity := false
  unit := false
  mirror := not
  superposable := fun first second => first = second
  belongsTo := fun unit entity => unit = entity
  localChange := fun first second => second = !first
  stereoisomers := fun first second => first ≠ second

theorem stereogenicUnitsWitness_judged :
    P92StereogenicUnitsJudged stereogenicUnitsWitness := by
  simp [P92StereogenicUnitsJudged, stereogenicUnitsWitness,
    BlueBookP92.IsStereogenicUnit, BlueBookP92.ChiralEntityHasStereogenicUnit,
    BlueBookP92.IsChiral, BlueBookP92.IsAchiral]

def chiralityDefinitionWitness : P92ChiralityAuthorityObservation where
  entity := false
  mirror := not
  superposable := fun first second => first = second
  classification := .chiral

theorem chiralityDefinitionWitness_judged :
    p92ChiralityDefinitionReference.Judges witnessInput chiralityDefinitionWitness := by
  simp [p92ChiralityDefinitionReference, chiralityDefinitionWitness, BlueBookP92.IsChiral]

def chiralityCenterWitness : P92ChiralityCenterAuthorityObservation where
  observation :=
    { ligand := fun position => position.val
      configuration := 0
      afterSwap := fun _first _second => 1 }
  distinguishable := fun first second => first ≠ second
  stereoisomers := fun first second => first ≠ second

theorem chiralityCenterWitness_judged :
    p92ChiralityCenterDefinitionReference.Judges witnessInput chiralityCenterWitness := by
  constructor
  · intro first second distinct
    dsimp [chiralityCenterWitness]
    intro sameValue
    exact distinct (Fin.ext sameValue)
  · intro first second _distinct
    simp [chiralityCenterWitness]

def chiralityAxisWitness : BlueBookP92.ChiralityAxisObservation where
  nearPairDistinguishable := True
  farPairDistinguishable := True
  arrangementNotSuperposableOnMirror := True

def chiralityPlaneWitness : BlueBookP92.ChiralityPlaneObservation where
  hasPlanarUnit := True
  hasAdjacentOutOfPlaneBond := True
  torsionRestricted := True
  planeCannotBeSymmetryPlane := True

def pseudoLigand (position : Fin 4) : Nat := position.val

def pseudoEnantiomorphic (first second : Nat) : Prop :=
  (first = 0 ∧ second = 1) ∨ (first = 1 ∧ second = 0)

theorem pseudoLigand_isPseudoasymmetric :
    BlueBookP92.IsPseudoasymmetricUnit pseudoLigand (fun first second => first ≠ second)
      pseudoEnantiomorphic := by
  constructor
  · intro first second distinct sameValue
    exact distinct (Fin.ext sameValue)
  · refine ⟨0, 1, by decide, ?_, ?_⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · intro otherFirst otherSecond _distinct enantiomorphic
      rcases enantiomorphic with enantiomorphic | enantiomorphic
      · left
        constructor <;> apply Fin.ext
        · exact enantiomorphic.1
        · exact enantiomorphic.2
      · right
        constructor <;> apply Fin.ext
        · exact enantiomorphic.1
        · exact enantiomorphic.2

def pseudoDescriptorBehaviourWitness : P92PseudoDescriptorBehaviour where
  descriptor := .r
  reflectedDescriptor := .r
  descriptorAfterLigandExchange := .s

theorem pseudoDescriptorBehaviourWitness_judged :
    PseudoDescriptorBehaviourJudged pseudoDescriptorBehaviourWitness := by
  decide

def pseudoasymmetricUnitWitness : P92PseudoasymmetricUnitAuthorityObservation :=
  .center
    { ligand := pseudoLigand
      distinguishable := fun first second => first ≠ second
      enantiomorphic := pseudoEnantiomorphic
      behaviour := pseudoDescriptorBehaviourWitness }

def cisTransDoubleBondWitness : BlueBookP92.DoubleBondUnitObservation where
  firstEndLigandsDifferent := True
  secondEndLigandsDifferent := True
  interchangeGeneratesCisTransIsomer := True

def enantiomorphicDoubleBondWitness : BlueBookP92.EnantiomorphicDoubleBondObservation where
  firstEndLigandsDifferent := True
  secondEndLigandsEnantiomorphic := True
  bondArrangementStereogenic := True

def priorityFrameWitness : P92FinitePriorityGeometryFrame where
  priorities := [1, 2, 3, 4]

def centerChiralityRuleWitness : P92CenterChiralityRuleAuthorityObservation where
  frame := priorityFrameWitness
  priorityPath := .clockwise [0, 1, 2]
  leastPriorityPosition := 3
  pseudoasymmetric := false
  viewedFromSideRemoteFromLowestPriority := True
  descriptor := .R

theorem centerChiralityRuleWitness_judged :
    p92CenterChiralityRuleReference.Judges witnessInput centerChiralityRuleWitness := by
  simp [p92CenterChiralityRuleReference, centerChiralityRuleWitness, priorityFrameWitness,
    StrictPriorityProgression, PriorityPathBackedByFrame, P92FinitePriorityGeometryFrame.priorityAt,
    P92OrientedPriorityPath.donorPositions, P92OrientedPriorityPath.sense,
    BlueBookP92.centerDescriptor]

def axisChiralityRuleWitness : P92AxisChiralityRuleAuthorityObservation where
  frame := priorityFrameWitness
  nearEndPositions := [0, 1]
  farEndPositions := [2, 3]
  nearSeniorPosition := 0
  nearJuniorPosition := 1
  farSeniorPosition := 2
  farJuniorPosition := 3
  priorityPath := .clockwise [0, 1, 2]
  viewedFromNearSeniorTowardFarJunior := True
  descriptor := .Ra

theorem axisChiralityRuleWitness_judged :
    P92AxisChiralityRuleJudged axisChiralityRuleWitness := by
  simp [P92AxisChiralityRuleJudged, axisChiralityRuleWitness, priorityFrameWitness,
    PriorityPathBackedByFrame, P92FinitePriorityGeometryFrame.priorityAt,
    P92OrientedPriorityPath.donorPositions, P92OrientedPriorityPath.sense,
    BlueBookP92.axialDescriptor]

def planeChiralityRuleWitness : P92PlaneChiralityRuleAuthorityObservation where
  frame := priorityFrameWitness
  derivedPriorityPath := .clockwise [0, 1, 2]
  leastPriorityPosition := 3
  derivedTetrahedronConstructed := True
  descriptor := .Rp

theorem planeChiralityRuleWitness_judged :
    P92PlaneChiralityRuleJudged planeChiralityRuleWitness := by
  simp [P92PlaneChiralityRuleJudged, planeChiralityRuleWitness, priorityFrameWitness,
    StrictPriorityProgression, PriorityPathBackedByFrame, P92FinitePriorityGeometryFrame.priorityAt,
    P92OrientedPriorityPath.donorPositions, P92OrientedPriorityPath.sense,
    BlueBookP92.planarDescriptor]

def helicityRuleWitness : P92HelicityRuleAuthorityObservation where
  entityKind := .helix
  referenceGroups := [10, 20, 30]
  orientedPath := .rightHanded [0, 1, 2]
  descriptor := .P

theorem helicityRuleWitness_judged : P92HelicityRuleJudged helicityRuleWitness := by
  decide

def helicityAxisWitness : P92HelicityAxisAuthorityObservation where
  frame := priorityFrameWitness
  nearEndPositions := [0, 1]
  farEndPositions := [2, 3]
  nearSeniorPosition := 0
  farSeniorPosition := 2
  orientedPath := .clockwise [0, 2]
  viewedAlongAxisFromNearToFar := True
  descriptor := .P

theorem helicityAxisWitness_judged : P92HelicityAxisJudged helicityAxisWitness := by
  simp [P92HelicityAxisJudged, helicityAxisWitness, priorityFrameWitness,
    PriorityPathBackedByFrame, P92FinitePriorityGeometryFrame.priorityAt,
    P92OrientedPriorityPath.donorPositions, P92OrientedPriorityPath.sense,
    BlueBookP92.axialHelicityDescriptor]

def helicityPlaneWitness : P92HelicityPlaneAuthorityObservation where
  frame := { priorities := [1, 2, 3] }
  referencePlanePositions := [0, 1]
  torsionConstruction := .negative 0 1 2
  descriptor := some .M

theorem helicityPlaneWitness_judged : P92HelicityPlaneJudged helicityPlaneWitness := by
  simp [P92HelicityPlaneJudged, helicityPlaneWitness,
    P92PlanarTorsionConstruction.firstInPlane, P92PlanarTorsionConstruction.secondInPlane,
    P92PlanarTorsionConstruction.attachedReference, P92PlanarTorsionConstruction.signedTorsion,
    P92FinitePriorityGeometryFrame.priorityAt, BlueBookP92.planarHelicityDescriptor?]

def dentateGraphWitness : P92LigandBondGraph where
  ligandAtoms := [0, 1, 2]
  coreAtoms := [3]
  bonds := [(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1),
    (0, 3), (1, 3), (2, 3)]

def ligandDentateKindsWitness : P92LigandDentateKindsAuthorityObservation where
  graph := dentateGraphWitness
  coordinationCore := 3
  donorAtoms := [0, 1, 2]
  cyclic := true
  denticity := .nDentate 3 (by omega)

theorem dentateGraphWitness_connected
    (first : Nat) (firstMember : first ∈ dentateGraphWitness.ligandAtoms)
    (last : Nat) (lastMember : last ∈ dentateGraphWitness.ligandAtoms) :
    ∃ path,
      P92BondPath dentateGraphWitness first last path ∧
        ∀ atom ∈ path, atom ∈ dentateGraphWitness.ligandAtoms := by
  simp [dentateGraphWitness] at firstMember lastMember
  rcases firstMember with rfl | rfl | rfl <;>
    rcases lastMember with rfl | rfl | rfl
  · exact ⟨[0], by simp [P92BondPath, dentateGraphWitness], by simp [dentateGraphWitness]⟩
  · exact ⟨[0, 1], by simp [P92BondPath, P92LigandBondGraph.Bonded, dentateGraphWitness],
      by simp [dentateGraphWitness]⟩
  · exact ⟨[0, 2], by simp [P92BondPath, P92LigandBondGraph.Bonded, dentateGraphWitness],
      by simp [dentateGraphWitness]⟩
  · exact ⟨[1, 0], by simp [P92BondPath, P92LigandBondGraph.Bonded, dentateGraphWitness],
      by simp [dentateGraphWitness]⟩
  · exact ⟨[1], by simp [P92BondPath, dentateGraphWitness], by simp [dentateGraphWitness]⟩
  · exact ⟨[1, 2], by simp [P92BondPath, P92LigandBondGraph.Bonded, dentateGraphWitness],
      by simp [dentateGraphWitness]⟩
  · exact ⟨[2, 0], by simp [P92BondPath, P92LigandBondGraph.Bonded, dentateGraphWitness],
      by simp [dentateGraphWitness]⟩
  · exact ⟨[2, 1], by simp [P92BondPath, P92LigandBondGraph.Bonded, dentateGraphWitness],
      by simp [dentateGraphWitness]⟩
  · exact ⟨[2], by simp [P92BondPath, dentateGraphWitness], by simp [dentateGraphWitness]⟩

theorem ligandDentateKindsWitness_judged :
    P92LigandDentateKindsJudged ligandDentateKindsWitness := by
  simp only [P92LigandDentateKindsJudged, ligandDentateKindsWitness]
  refine ⟨by decide, by decide, ?_, by decide, ?_, by simp [dentateGraphWitness],
    ?_, ?_, ?_, ?_⟩
  · simp [dentateGraphWitness]
  · simp [dentateGraphWitness]
  · simp [P92GraphDerivedDonorSet, P92LigandBondGraph.Bonded, dentateGraphWitness]
  · exact dentateGraphWitness_connected
  · constructor
    · intro _cyclic
      refine ⟨[0, 1, 2], ?_, by simp [dentateGraphWitness]⟩
      refine ⟨by decide, by decide, ?_, ?_⟩
      · simp [P92LigandBondGraph.Bonded, dentateGraphWitness]
      · exact ⟨0, 2, rfl, rfl, by simp [P92LigandBondGraph.Bonded, dentateGraphWitness]⟩
    · intro _cycle
      trivial
  · rfl

def sequenceRuleHierarchyWitness : P92SequenceRuleHierarchyAuthorityObservation where
  model :=
    { caseCount := 1
      evaluation := fun _rule _caseIndex => some .lt }
  decision := some (.rule1a, .lt)

theorem sequenceRuleHierarchyWitness_judged :
    P92SequenceRuleHierarchyJudged sequenceRuleHierarchyWitness := by
  decide

/-- Molecular input is definitionally irrelevant to these 21 conceptual source references. -/
theorem reference_input_invariant
    (row : Next54P92FoundationalAuthorityRow)
    (first second : AuthoritativeChemicalInput) :
    (row.reference.Applicable first ↔ row.reference.Applicable second) ∧
      ∀ observation,
        row.reference.Judges first observation ↔
          row.reference.Judges second observation := by
  cases row <;> exact ⟨Iff.rfl, fun _observation => Iff.rfl⟩

/-- All 21 foundational source relations are satisfiable.  This theorem establishes consistency
of input-invariant conceptual references, not chemical realization by `witnessInput`. -/
theorem reference_nonvacuous (row : Next54P92FoundationalAuthorityRow) :
    ∃ observation,
      row.reference.Applicable witnessInput ∧
        row.reference.Judges witnessInput observation := by
  cases row with
  | stereogenicUnits =>
      exact ⟨stereogenicUnitsWitness, trivial, stereogenicUnitsWitness_judged⟩
  | chiralityDefinition =>
      exact ⟨chiralityDefinitionWitness, trivial, chiralityDefinitionWitness_judged⟩
  | chiralityCenterDefinition =>
      exact ⟨chiralityCenterWitness, trivial, chiralityCenterWitness_judged⟩
  | chiralityAxisDefinition =>
      exact ⟨chiralityAxisWitness, trivial, by simp [reference, p92ChiralityAxisDefinitionReference,
        BlueBookP92.IsChiralityAxis, chiralityAxisWitness]⟩
  | chiralityPlaneDefinition =>
      exact ⟨chiralityPlaneWitness, trivial, by simp [reference,
        p92ChiralityPlaneDefinitionReference, BlueBookP92.IsChiralityPlane,
        chiralityPlaneWitness]⟩
  | pseudoasymmetricUnitDefinition =>
      exact ⟨pseudoasymmetricUnitWitness, trivial, by
        exact ⟨pseudoLigand_isPseudoasymmetric, pseudoDescriptorBehaviourWitness_judged⟩⟩
  | cisTransDoubleBondUnitDefinition =>
      exact ⟨cisTransDoubleBondWitness, trivial, by simp [reference,
        p92CisTransDoubleBondUnitDefinitionReference, BlueBookP92.IsCisTransDoubleBondUnit,
        cisTransDoubleBondWitness]⟩
  | enantiomorphicDoubleBondUnitDefinition =>
      exact ⟨enantiomorphicDoubleBondWitness, trivial, by simp [reference,
        p92EnantiomorphicDoubleBondUnitDefinitionReference,
        BlueBookP92.IsEnantiomorphicDoubleBond, enantiomorphicDoubleBondWitness]⟩
  | bondingNumberScope =>
      change ∃ bondingNumber : Nat, True ∧ BlueBookP92.WithinBondingNumberScope bondingNumber
      exact ⟨6, trivial, BlueBookP92.bonding_number_six_is_in_scope⟩
  | chiralityRuleGeneral =>
      exact ⟨.center centerChiralityRuleWitness, trivial, centerChiralityRuleWitness_judged⟩
  | centerChiralityRule =>
      exact ⟨centerChiralityRuleWitness, trivial, centerChiralityRuleWitness_judged⟩
  | axisChiralityRule =>
      exact ⟨axisChiralityRuleWitness, trivial, axisChiralityRuleWitness_judged⟩
  | planeChiralityRule =>
      exact ⟨planeChiralityRuleWitness, trivial, planeChiralityRuleWitness_judged⟩
  | helicityRule =>
      exact ⟨helicityRuleWitness, trivial, helicityRuleWitness_judged⟩
  | helicityAxis =>
      exact ⟨helicityAxisWitness, trivial, helicityAxisWitness_judged⟩
  | helicityPlane =>
      exact ⟨helicityPlaneWitness, trivial, helicityPlaneWitness_judged⟩
  | rsmpDescriptorCorrespondence =>
      exact ⟨{ application := .axis, helicity := .M, descriptor := .R }, trivial, rfl⟩
  | sequenceRulePropertyClasses =>
      exact ⟨{ input := .rule1a, output := .materialOrTopological }, trivial, rfl⟩
  | sequenceRuleReflectionBehavior =>
      exact ⟨{ input := .rule5, output := .variant }, trivial, rfl⟩
  | ligandDentateKinds =>
      exact ⟨ligandDentateKindsWitness, trivial, ligandDentateKindsWitness_judged⟩
  | sequenceRuleHierarchy =>
      exact ⟨sequenceRuleHierarchyWitness, trivial, sequenceRuleHierarchyWitness_judged⟩

/-- Reference satisfiability transports to every input because the conceptual relations are
input-invariant. -/
theorem reference_nonvacuous_at
    (row : Next54P92FoundationalAuthorityRow)
    (input : AuthoritativeChemicalInput) :
    ∃ observation,
      row.reference.Applicable input ∧
        row.reference.Judges input observation := by
  rcases row.reference_nonvacuous with ⟨observation, applicable, judged⟩
  have invariant := row.reference_input_invariant witnessInput input
  exact ⟨observation, invariant.1.mp applicable, (invariant.2 observation).mp judged⟩

end Next54P92FoundationalAuthorityRow

theorem next54P92Foundational_sourceAuditComplete
    {provision : IUPACNormativeProvision}
    (member : provision ∈ next54P92FoundationalProvisions) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  have sourceNotIncomplete :
      provision.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources := by
    have everySourceClosed : next54P92FoundationalProvisions.Forall (fun row =>
        row.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources) := by
      decide
    exact (List.forall_iff_forall_mem.mp everySourceClosed) provision member
  apply Classical.byContradiction
  intro auditIncomplete
  exact sourceNotIncomplete
    ((IUPACNormativeSource.mem_currentIncompleteProvisionAuditSources_iff
      provision.source).2 auditIncomplete)

theorem next54P92Foundational_mem_next54
    {provision : IUPACNormativeProvision}
    (member : provision ∈ next54P92FoundationalProvisions) :
    provision ∈ next54Provisions := by
  have p92Member : provision ∈ next54P92ResidualProvisions := by
    exact List.mem_append_left p92DigraphAndRule1aSemanticsSlice member
  have blueBookMember : provision ∈ next54BlueBookProvisions := by
    apply List.mem_append_right next54P91Provisions
    exact List.mem_append_left next54P93PolyhedralResidualProvisions p92Member
  exact List.mem_append_left next54IR9ResidualProvisions blueBookMember

theorem exists_next54P92FoundationalAuthorityRow
    {provision : IUPACNormativeProvision}
    (member : provision ∈ next54P92FoundationalProvisions) :
    ∃ row, row ∈ Next54P92FoundationalAuthorityRow.all ∧ row.provision = provision := by
  rw [← Next54P92FoundationalAuthorityRow.all_provisions_exact] at member
  simpa only [List.mem_map] using member

noncomputable def next54P92FoundationalAuthorityRowOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ next54P92FoundationalProvisions) :
    Next54P92FoundationalAuthorityRow :=
  Classical.choose (exists_next54P92FoundationalAuthorityRow member)

theorem next54P92FoundationalAuthorityRowOf_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ next54P92FoundationalProvisions) :
    (next54P92FoundationalAuthorityRowOf provision member).provision = provision :=
  (Classical.choose_spec (exists_next54P92FoundationalAuthorityRow member)).2

structure Next54P92FoundationalReviewedSemanticsTable where
  reviewed : ReviewedProvisionBatch next54P92FoundationalProvisions.toFinset
  classifier_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ next54P92FoundationalProvisions.toFinset),
      (reviewed.row provision member).kind =
        next54Kind provision (next54P92Foundational_mem_next54 (by simpa using member))

noncomputable def next54P92FoundationalReviewedSemantics :
    Next54P92FoundationalReviewedSemanticsTable where
  reviewed :=
    { ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
      row := fun provision member =>
        (next54P92FoundationalAuthorityRowOf provision (by simpa using member)).semantics
      sourceAudited := by
        intro provision member
        exact next54P92Foundational_sourceAuditComplete (by simpa using member) }
  classifier_exact := by
    intro provision member
    let row := next54P92FoundationalAuthorityRowOf provision (by simpa using member)
    have rowProvision : row.provision = provision :=
      next54P92FoundationalAuthorityRowOf_provision provision (by simpa using member)
    have rowClassifier := Next54P92FoundationalAuthorityRow.classifier_exact row
    have totalClassifier := next54Kind?_eq_some provision
      (next54P92Foundational_mem_next54 (by simpa using member))
    rw [rowProvision] at rowClassifier
    change row.kind = next54Kind provision _
    exact Option.some.inj (rowClassifier.symm.trans totalClassifier)

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P92FoundationalAuthorityRow.all_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P92FoundationalAuthorityRow.classifier_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54P92Foundational_sourceAuditComplete
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54P92Foundational_mem_next54
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54P92FoundationalAuthorityRowOf_provision
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54P92FoundationalReviewedSemantics
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P92FoundationalAuthorityRow.witnessInput_structurallyWellFormed
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P92FoundationalAuthorityRow.reference_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54P92FoundationalAuthorityRow.reference_nonvacuous_at
