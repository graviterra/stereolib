import TetraStereo.OneCenter.ChemistrySemantics
import TetraStereo.OneCenter.P94Conformation

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Complete represented P-94 conformation pipeline

This module connects the independent P-94 relations to a molecule-bound executable report.  The
geometry boundary remains exact and proof relevant: callers supply torsion, plane-side, symmetry,
boat-interconversion, and in/out evidence.  The analyzer validates every referenced molecular
unit, emits every descriptor supported by the independent relation, and deliberately retains both
answers at the inclusive 30°, 90°, and 150° P-94 boundaries.
-/

open BlueBookP94

inductive P94ConformationUnitKind where
  | wholeMoleculeConformation
  | torsionAxis
  | fiveMemberedRing
  | sixMemberedRing
  | crownRing
  | eightMemberedTubRing
  | bicyclicBridge
  deriving DecidableEq, Repr

/-- A molecule-local physical carrier for one P-94 observation.  Atom numbers refer to the
certified raw molecule.  Ring carriers list one cyclic traversal.  A torsion carrier lists the
finite directed rotation-axis path `A-...-B` and records the selected front/rear participants;
those participants may be physical atoms, lone-pair phantoms, or multiple-bond duplicates. -/
structure P94ConformationUnit where
  kind : P94ConformationUnitKind
  atoms : List ℕ
  torsionParticipants? : Option (TorsionParticipant ℕ × TorsionParticipant ℕ) := none
  deriving DecidableEq, Repr

namespace P94ConformationUnit

def Bonded (molecule : RawMolecule) (left right : ℕ) : Prop :=
  ∃ bond ∈ molecule.bonds, bond.connects left right = true

def ConsecutivelyBonded (molecule : RawMolecule) (atoms : List ℕ) : Prop :=
  ∀ pair ∈ atoms.zip atoms.tail, Bonded molecule pair.1 pair.2

def CyclicallyBonded (molecule : RawMolecule) (atoms : List ℕ) : Prop :=
  ConsecutivelyBonded molecule atoms ∧
  ∃ first last,
    atoms.head? = some first ∧ atoms.reverse.head? = some last ∧
    Bonded molecule last first

/-- Successor list for one closed traversal.  For a nonempty traversal this has the same length as
`atoms` and pairs the final atom with the first. -/
def cyclicSuccessors (atoms : List ℕ) : List ℕ :=
  atoms.tail ++ atoms.take 1

/-- Actual molecular bond orders around the named closed traversal, including the closing edge. -/
def cycleBondOrders (unit : P94ConformationUnit) (molecule : RawMolecule) : List BondOrder :=
  List.zipWith molecule.bondOrder unit.atoms (cyclicSuccessors unit.atoms)

/-- Bond spellings that denote a constitutionally saturated single bond after certified
normalization.  Aromatic and unspecified spellings are intentionally not equated with saturation
merely because their coarse `BondOrder` projection is `1`. -/
def SaturatedSingleBondKind : ParsedBondKind → Prop
  | .single | .up | .down => True
  | .unspecified | .double | .triple | .aromatic => False

instance saturatedSingleBondKindDecidable (kind : ParsedBondKind) :
    Decidable (SaturatedSingleBondKind kind) := by
  cases kind <;> unfold SaturatedSingleBondKind <;> infer_instance

/-- Every raw bond record representing an edge of the named cycle has a saturated single-bond
kind.  This preserves information erased by the coarse numeric bond-order projection. -/
def SaturatedCycleBondKinds (unit : P94ConformationUnit) (molecule : RawMolecule) : Prop :=
  ∀ edge ∈ unit.atoms.zip (cyclicSuccessors unit.atoms),
    ∀ bond ∈ molecule.bonds,
      bond.connects edge.1 edge.2 = true → SaturatedSingleBondKind bond.kind

/-- The source's “saturated cyclic compound” premise, derived from the molecular graph rather
than accepted as an unconnected proposition in a geometry record. -/
def SaturatedCyclic (unit : P94ConformationUnit) (molecule : RawMolecule) : Prop :=
  (∀ order ∈ unit.cycleBondOrders molecule, order = 1) ∧
    unit.SaturatedCycleBondKinds molecule

/-- Number of actual double bonds in the named ring traversal. -/
def CycleDoubleBondCount (unit : P94ConformationUnit) (molecule : RawMolecule) : ℕ :=
  (unit.cycleBondOrders molecule).count 2

/-- Raw bond spellings allowed in a genuinely monounsaturated cycle. -/
def MonounsaturatedCycleBondKind : ParsedBondKind → Prop
  | .single | .up | .down | .double => True
  | .unspecified | .triple | .aromatic => False

instance monounsaturatedCycleBondKindDecidable (kind : ParsedBondKind) :
    Decidable (MonounsaturatedCycleBondKind kind) := by
  cases kind <;> unfold MonounsaturatedCycleBondKind <;> infer_instance

/-- Every record on every named cycle edge is either saturated single or the unique double-bond
kind; aromatic, triple, and unresolved spellings are excluded. -/
def MonounsaturatedCycleBondKinds
    (unit : P94ConformationUnit) (molecule : RawMolecule) : Prop :=
  ∀ edge ∈ unit.atoms.zip (cyclicSuccessors unit.atoms),
    ∀ bond ∈ molecule.bonds,
      bond.connects edge.1 edge.2 = true → MonounsaturatedCycleBondKind bond.kind

/-- Exact molecular meaning of a monounsaturated cyclic carrier: precisely one order-two edge and
no additional aromatic, triple, or unresolved cyclic bond. -/
def MonounsaturatedCyclic (unit : P94ConformationUnit) (molecule : RawMolecule) : Prop :=
  unit.CycleDoubleBondCount molecule = 1 ∧
    unit.MonounsaturatedCycleBondKinds molecule

theorem saturatedCyclic_iff_cycleBondOrders
    (unit : P94ConformationUnit) (molecule : RawMolecule) :
    unit.SaturatedCyclic molecule ↔
      (∀ order ∈ unit.cycleBondOrders molecule, order = 1) ∧
        unit.SaturatedCycleBondKinds molecule :=
  Iff.rfl

def ParticipantBounded (participant : TorsionParticipant ℕ) (atomCount : ℕ) : Prop :=
  match participant with
  | .atom atom | .lonePair atom | .duplicateAtom atom => atom < atomCount

/-- Molecular meaning of a P-94 terminal participant at one end of the rotation axis.  Ordinary
participants are bonded substituents; a lone pair belongs to the endpoint itself; and a duplicate
participant denotes an atom joined to the endpoint with bond order greater than one. -/
def ParticipantAttached (molecule : RawMolecule) (axisEndpoint : ℕ) :
    TorsionParticipant ℕ → Prop
  | .atom atom => 0 < molecule.bondOrder axisEndpoint atom
  | .lonePair center => center = axisEndpoint
  | .duplicateAtom original => 1 < molecule.bondOrder axisEndpoint original

/-- Exact endpoints of the finite directed rotation-axis path. -/
def AxisEndpoints (unit : P94ConformationUnit) (front rear : ℕ) : Prop :=
  unit.atoms.head? = some front ∧ unit.atoms.getLast? = some rear

/-- Molecular admission common to every result-producing P-94 evidence constructor. -/
def ValidFor (unit : P94ConformationUnit) (molecule : RawMolecule) : Prop :=
  unit.atoms.Nodup ∧
  (∀ atom ∈ unit.atoms, atom < molecule.atomCount) ∧
  match unit.kind with
  | .wholeMoleculeConformation =>
      unit.torsionParticipants? = none ∧ unit.atoms = List.range molecule.atomCount
  | .torsionAxis =>
      ∃ front rear axisFront axisRear,
        unit.torsionParticipants? = some (front, rear) ∧
        AxisEndpoints unit axisFront axisRear ∧
        2 ≤ unit.atoms.length ∧ ConsecutivelyBonded molecule unit.atoms ∧
        ParticipantBounded front molecule.atomCount ∧
        ParticipantBounded rear molecule.atomCount ∧
        ParticipantAttached molecule axisFront front ∧
        ParticipantAttached molecule axisRear rear
  | .fiveMemberedRing =>
      unit.torsionParticipants? = none ∧
        unit.atoms.length = 5 ∧ CyclicallyBonded molecule unit.atoms
  | .sixMemberedRing =>
      unit.torsionParticipants? = none ∧
        unit.atoms.length = 6 ∧ CyclicallyBonded molecule unit.atoms
  | .crownRing =>
      unit.torsionParticipants? = none ∧
        8 ≤ unit.atoms.length ∧ Even unit.atoms.length ∧
        CyclicallyBonded molecule unit.atoms
  | .eightMemberedTubRing =>
      unit.torsionParticipants? = none ∧
        unit.atoms.length = 8 ∧ CyclicallyBonded molecule unit.atoms
  | .bicyclicBridge =>
      unit.torsionParticipants? = none ∧
        2 ≤ unit.atoms.length ∧ ConsecutivelyBonded molecule unit.atoms

theorem torsionAxis_validFor_iff (unit : P94ConformationUnit) (molecule : RawMolecule)
    (torsionKind : unit.kind = .torsionAxis) :
    unit.ValidFor molecule ↔
      unit.atoms.Nodup ∧
      (∀ atom ∈ unit.atoms, atom < molecule.atomCount) ∧
      ∃ front rear axisFront axisRear,
        unit.torsionParticipants? = some (front, rear) ∧
        AxisEndpoints unit axisFront axisRear ∧
        2 ≤ unit.atoms.length ∧ ConsecutivelyBonded molecule unit.atoms ∧
        ParticipantBounded front molecule.atomCount ∧
        ParticipantBounded rear molecule.atomCount ∧
        ParticipantAttached molecule axisFront front ∧
        ParticipantAttached molecule axisRear rear := by
  unfold ValidFor
  rw [torsionKind]

end P94ConformationUnit

inductive P94ConformationDescriptor where
  | conformerPair
  | torsionSense (sense : RotationSense)
  | torsionClass (classification : ConformationalClass)
  | eclipsed
  | staggered
  | bisecting
  | eclipsing
  | sCis
  | sTrans
  | envelope
  | chair
  | boat
  | twist
  | halfChair
  | crown
  | tub
  | inOut
  deriving DecidableEq, Repr

namespace P94ConformationDescriptor

def all : List P94ConformationDescriptor :=
  [ .conformerPair
  , .torsionSense .clockwise
  , .torsionSense .anticlockwise
  , .torsionClass .synperiplanar
  , .torsionClass .synclinal
  , .torsionClass .anticlinal
  , .torsionClass .antiperiplanar
  , .eclipsed
  , .staggered
  , .bisecting
  , .eclipsing
  , .sCis
  , .sTrans
  , .envelope
  , .chair
  , .boat
  , .twist
  , .halfChair
  , .crown
  , .tub
  , .inOut
  ]

theorem mem_all (descriptor : P94ConformationDescriptor) : descriptor ∈ all := by
  cases descriptor with
  | conformerPair => simp [all]
  | torsionSense sense => cases sense <;> simp [all]
  | torsionClass classification => cases classification <;> simp [all]
  | eclipsed | staggered | bisecting | eclipsing | sCis | sTrans | envelope | chair | boat |
      twist | halfChair | crown | tub | inOut => simp [all]

end P94ConformationDescriptor

/-- A P-94 torsion candidate paired with the physical, lone-pair, or duplicate participant whose
priority data it represents. -/
structure P94TorsionSelectionCandidate where
  participant : TorsionParticipant ℕ
  ranking : TorsionCandidate

structure P94TorsionEvidence where
  unit : P94ConformationUnit
  frame : SelectedTorsionFrame ℕ
  frontCandidates : List P94TorsionSelectionCandidate
  rearCandidates : List P94TorsionSelectionCandidate
  selectedFront : P94TorsionSelectionCandidate
  selectedRear : P94TorsionSelectionCandidate
  rotationSense : RotationSense

namespace P94TorsionEvidence

def ParticipantBounded (participant : TorsionParticipant ℕ) (atomCount : ℕ) : Prop :=
  P94ConformationUnit.ParticipantBounded participant atomCount

def CandidateParticipantsBounded (record : P94TorsionEvidence) (atomCount : ℕ) : Prop :=
  ParticipantBounded record.selectedFront.participant atomCount ∧
  ParticipantBounded record.selectedRear.participant atomCount ∧
  ∀ candidate ∈ record.frontCandidates ++ record.rearCandidates,
    ParticipantBounded candidate.participant atomCount

/-- Every priority candidate belongs to the appropriate molecular end of the named axis, and the
frame itself uses exactly the typed participants stored in the physical carrier. -/
def AxisParticipantsValid (record : P94TorsionEvidence) (molecule : RawMolecule) : Prop :=
  ∃ front rear axisFront axisRear,
    record.unit.torsionParticipants? = some (front, rear) ∧
    record.frame.front = front ∧ record.frame.rear = rear ∧
    record.unit.AxisEndpoints axisFront axisRear ∧
    (∀ candidate ∈ record.frontCandidates,
      P94ConformationUnit.ParticipantAttached molecule axisFront candidate.participant) ∧
    (∀ candidate ∈ record.rearCandidates,
      P94ConformationUnit.ParticipantAttached molecule axisRear candidate.participant)

def SelectedBySourceCriteria (record : P94TorsionEvidence) : Prop :=
  record.selectedFront ∈ record.frontCandidates ∧
  record.selectedRear ∈ record.rearCandidates ∧
  record.frame.front = record.selectedFront.participant ∧
  record.frame.rear = record.selectedRear.participant ∧
  TorsionCandidate.SelectedByP94Criteria
    (record.frontCandidates.map P94TorsionSelectionCandidate.ranking)
    record.selectedFront.ranking ∧
  TorsionCandidate.SelectedByP94Criteria
    (record.rearCandidates.map P94TorsionSelectionCandidate.ranking)
    record.selectedRear.ranking

end P94TorsionEvidence

structure P94ConformerEvidence (State : Type*) where
  unit : P94ConformationUnit
  singleBondRotation : State → State → Prop
  first : State
  second : State

structure P94EclipsedStaggeredEvidence where
  unit : P94ConformationUnit
  angle : TorsionAngle
  staggeredContext : StaggeredContext

structure P94TrigonalConformationEvidence where
  unit : P94ConformationUnit
  observation : TrigonalConformationObservation

structure P94ConjugatedSystemEvidence where
  unit : P94ConformationUnit
  system : ConjugatedSystemKind
  angle : TorsionAngle

structure P94RingPlaneEvidence where
  unit : P94ConformationUnit
  sides : List PlaneSide
  saturatedCyclic : Prop
  symmetricallyEquivalent : Prop
  /-- Explicit applicability of the carbohydrate-specific five-ring twist convention. -/
  carbohydrateFiveRing : Prop := False

structure P94TwistEvidence (State : Type*) where
  unit : P94ConformationUnit
  singleBondRotation : State → State → Prop
  endpointConformationsDistinct : State → State → Prop
  isBoatState : State → Prop
  isChairState : State → Prop
  candidate : State
  firstLeg : List State
  secondLeg : List State

structure P94HalfChairEvidence where
  unit : P94ConformationUnit
  observation : HalfChairObservation

structure P94InOutEvidence (Framework : Type*) where
  unit : P94ConformationUnit
  first : InOutObservation Framework
  second : InOutObservation Framework
  bicyclicSystem : Prop

inductive P94ConformationEvidence (State Framework : Type*) where
  | conformer (record : P94ConformerEvidence State)
  | torsion (record : P94TorsionEvidence)
  | eclipsedStaggered (record : P94EclipsedStaggeredEvidence)
  | trigonal (record : P94TrigonalConformationEvidence)
  | conjugated (record : P94ConjugatedSystemEvidence)
  | ringPlane (record : P94RingPlaneEvidence)
  | twist (record : P94TwistEvidence State)
  | halfChair (record : P94HalfChairEvidence)
  | inOut (record : P94InOutEvidence Framework)

namespace P94ConformationEvidence

def unit {State Framework : Type*} :
    P94ConformationEvidence State Framework → P94ConformationUnit
  | .conformer record => record.unit
  | .torsion record => record.unit
  | .eclipsedStaggered record => record.unit
  | .trigonal record => record.unit
  | .conjugated record => record.unit
  | .ringPlane record => record.unit
  | .twist record => record.unit
  | .halfChair record => record.unit
  | .inOut record => record.unit

/-- Independent descriptor relation, stated only with the P-94 predicates and explicit molecular
role evidence.  No executable analyzer appears in this definition. -/
def Supports {State Framework : Type*} :
    P94ConformationEvidence State Framework → P94ConformationDescriptor → Prop
  | .conformer record, .conformerPair =>
      record.unit.kind = .wholeMoleculeConformation ∧
        AreConformers record.singleBondRotation record.first record.second
  | .torsion record, .torsionSense sense =>
      record.unit.kind = .torsionAxis ∧ record.rotationSense = sense ∧
        SignAgreesWithRotation record.frame.angle sense
  | .torsion record, .torsionClass classification =>
      record.unit.kind = .torsionAxis ∧ record.SelectedBySourceCriteria ∧
      ClassifiedAs record.frame.angle classification
  | .eclipsedStaggered record, .eclipsed =>
      record.unit.kind = .torsionAxis ∧
        record.staggeredContext.allLigandsIdentical ∧ Eclipsed record.angle
  | .eclipsedStaggered record, .staggered =>
      record.unit.kind = .torsionAxis ∧ IsStaggered record.staggeredContext record.angle
  | .trigonal record, .bisecting =>
      record.unit.kind = .torsionAxis ∧ IsBisectingConformation record.observation
  | .trigonal record, .eclipsing =>
      record.unit.kind = .torsionAxis ∧ IsEclipsingConformation record.observation
  | .conjugated record, .sCis =>
      record.unit.kind = .torsionAxis ∧ SCisTransApplies record.system record.angle .sCis
  | .conjugated record, .sTrans =>
      record.unit.kind = .torsionAxis ∧ SCisTransApplies record.system record.angle .sTrans
  | .ringPlane record, .envelope =>
      record.unit.kind = .fiveMemberedRing ∧
        record.sides.length = record.unit.atoms.length ∧ IsEnvelope record.sides
  | .ringPlane record, .chair =>
      record.unit.kind = .sixMemberedRing ∧
        record.sides.length = record.unit.atoms.length ∧ IsChair record.sides
  | .ringPlane record, .boat =>
      record.unit.kind = .sixMemberedRing ∧
        record.sides.length = record.unit.atoms.length ∧ IsBoat record.sides
  | .ringPlane record, .twist =>
      record.unit.kind = .fiveMemberedRing ∧
        record.sides.length = record.unit.atoms.length ∧
        record.carbohydrateFiveRing ∧ IsCarbohydrateFiveRingTwist record.sides
  | .ringPlane record, .crown =>
      record.unit.kind = .crownRing ∧
        record.sides.length = record.unit.atoms.length ∧ record.saturatedCyclic ∧
        IsCrown record.sides record.symmetricallyEquivalent
  | .ringPlane record, .tub =>
      record.unit.kind = .eightMemberedTubRing ∧
        record.sides.length = record.unit.atoms.length ∧ IsTub record.sides
  | .twist record, .twist =>
      record.unit.kind = .sixMemberedRing ∧
        ExplicitTwistOnBoatInterconversion record.singleBondRotation
          record.endpointConformationsDistinct record.isBoatState record.isChairState record.candidate
          record.firstLeg record.secondLeg
  | .halfChair record, .halfChair =>
      record.unit.kind = .sixMemberedRing ∧ IsHalfChair record.observation
  | .inOut record, .inOut =>
      record.unit.kind = .bicyclicBridge ∧ record.bicyclicSystem ∧
        AreInOutIsomers record.first record.second
  | _, _ => False

/-- Molecule-relative validity not already carried by the abstract P-94 predicates.  In
particular, every physical/lone-pair/duplicate torsion participant must refer to an atom of the
certified molecule. -/
def MolecularRolesValid {State Framework : Type*}
    (record : P94ConformationEvidence State Framework) (molecule : RawMolecule) : Prop :=
  match record with
  | .torsion torsionRecord =>
      torsionRecord.CandidateParticipantsBounded molecule.atomCount ∧
        torsionRecord.AxisParticipantsValid molecule
  | .ringPlane ringRecord =>
      match ringRecord.unit.kind with
      | .crownRing => ringRecord.unit.SaturatedCyclic molecule
      | _ => True
  | .halfChair halfChairRecord =>
      halfChairRecord.observation.doubleBondCount =
        halfChairRecord.unit.CycleDoubleBondCount molecule ∧
      halfChairRecord.unit.MonounsaturatedCyclic molecule
  | _ => True

end P94ConformationEvidence

namespace P94TorsionEvidence

theorem molecularRolesValid_iff_axisParticipants {State Framework : Type*}
    (record : P94TorsionEvidence) (molecule : RawMolecule) :
    (P94ConformationEvidence.torsion record :
        P94ConformationEvidence State Framework).MolecularRolesValid molecule ↔
      record.CandidateParticipantsBounded molecule.atomCount ∧
        record.AxisParticipantsValid molecule :=
  Iff.rfl

end P94TorsionEvidence

namespace P94RingPlaneEvidence

theorem molecularRolesValid_iff_crownSaturation {State Framework : Type*}
    (record : P94RingPlaneEvidence) (molecule : RawMolecule)
    (crownKind : record.unit.kind = .crownRing) :
    (P94ConformationEvidence.ringPlane record :
        P94ConformationEvidence State Framework).MolecularRolesValid molecule ↔
      record.unit.SaturatedCyclic molecule := by
  simp [P94ConformationEvidence.MolecularRolesValid, crownKind]

end P94RingPlaneEvidence

namespace P94HalfChairEvidence

theorem molecularRolesValid_iff_doubleBondCount {State Framework : Type*}
    (record : P94HalfChairEvidence) (molecule : RawMolecule) :
    (P94ConformationEvidence.halfChair record :
        P94ConformationEvidence State Framework).MolecularRolesValid molecule ↔
      record.observation.doubleBondCount = record.unit.CycleDoubleBondCount molecule ∧
        record.unit.MonounsaturatedCyclic molecule :=
  Iff.rfl

end P94HalfChairEvidence

theorem p94ConformerSupport_iff {State Framework : Type*}
    (record : P94ConformerEvidence State) :
    P94ConformationEvidence.Supports
        (.conformer record : P94ConformationEvidence State Framework) .conformerPair ↔
      record.unit.kind = .wholeMoleculeConformation ∧
        AreConformers record.singleBondRotation record.first record.second :=
  Iff.rfl

theorem p94TorsionSenseSupport_iff {State Framework : Type*}
    (record : P94TorsionEvidence) (sense : RotationSense) :
    P94ConformationEvidence.Supports
        (.torsion record : P94ConformationEvidence State Framework) (.torsionSense sense) ↔
      record.unit.kind = .torsionAxis ∧ record.rotationSense = sense ∧
        SignAgreesWithRotation record.frame.angle sense :=
  Iff.rfl

theorem p94TorsionClassSupport_iff {State Framework : Type*}
    (record : P94TorsionEvidence) (classification : ConformationalClass) :
    P94ConformationEvidence.Supports
        (.torsion record : P94ConformationEvidence State Framework)
        (.torsionClass classification) ↔
      record.unit.kind = .torsionAxis ∧ record.SelectedBySourceCriteria ∧
        ClassifiedAs record.frame.angle classification :=
  Iff.rfl

theorem p94EclipsedSupport_iff {State Framework : Type*}
    (record : P94EclipsedStaggeredEvidence) :
    P94ConformationEvidence.Supports
        (.eclipsedStaggered record : P94ConformationEvidence State Framework) .eclipsed ↔
      record.unit.kind = .torsionAxis ∧
        record.staggeredContext.allLigandsIdentical ∧ Eclipsed record.angle :=
  Iff.rfl

theorem p94StaggeredSupport_iff {State Framework : Type*}
    (record : P94EclipsedStaggeredEvidence) :
    P94ConformationEvidence.Supports
        (.eclipsedStaggered record : P94ConformationEvidence State Framework) .staggered ↔
      record.unit.kind = .torsionAxis ∧ IsStaggered record.staggeredContext record.angle :=
  Iff.rfl

theorem p94BisectingSupport_iff {State Framework : Type*}
    (record : P94TrigonalConformationEvidence) :
    P94ConformationEvidence.Supports
        (.trigonal record : P94ConformationEvidence State Framework) .bisecting ↔
      record.unit.kind = .torsionAxis ∧ IsBisectingConformation record.observation :=
  Iff.rfl

theorem p94EclipsingSupport_iff {State Framework : Type*}
    (record : P94TrigonalConformationEvidence) :
    P94ConformationEvidence.Supports
        (.trigonal record : P94ConformationEvidence State Framework) .eclipsing ↔
      record.unit.kind = .torsionAxis ∧ IsEclipsingConformation record.observation :=
  Iff.rfl

theorem p94SCisSupport_iff {State Framework : Type*}
    (record : P94ConjugatedSystemEvidence) :
    P94ConformationEvidence.Supports
        (.conjugated record : P94ConformationEvidence State Framework) .sCis ↔
      record.unit.kind = .torsionAxis ∧ SCisTransApplies record.system record.angle .sCis :=
  Iff.rfl

theorem p94STransSupport_iff {State Framework : Type*}
    (record : P94ConjugatedSystemEvidence) :
    P94ConformationEvidence.Supports
        (.conjugated record : P94ConformationEvidence State Framework) .sTrans ↔
      record.unit.kind = .torsionAxis ∧ SCisTransApplies record.system record.angle .sTrans :=
  Iff.rfl

theorem p94EnvelopeSupport_iff {State Framework : Type*} (record : P94RingPlaneEvidence) :
    P94ConformationEvidence.Supports
        (.ringPlane record : P94ConformationEvidence State Framework) .envelope ↔
      record.unit.kind = .fiveMemberedRing ∧
        record.sides.length = record.unit.atoms.length ∧ IsEnvelope record.sides :=
  Iff.rfl

theorem p94ChairSupport_iff {State Framework : Type*} (record : P94RingPlaneEvidence) :
    P94ConformationEvidence.Supports
        (.ringPlane record : P94ConformationEvidence State Framework) .chair ↔
      record.unit.kind = .sixMemberedRing ∧
        record.sides.length = record.unit.atoms.length ∧ IsChair record.sides :=
  Iff.rfl

theorem p94BoatSupport_iff {State Framework : Type*} (record : P94RingPlaneEvidence) :
    P94ConformationEvidence.Supports
        (.ringPlane record : P94ConformationEvidence State Framework) .boat ↔
      record.unit.kind = .sixMemberedRing ∧
        record.sides.length = record.unit.atoms.length ∧ IsBoat record.sides :=
  Iff.rfl

theorem p94CarbohydrateFiveRingTwistSupport_iff {State Framework : Type*}
    (record : P94RingPlaneEvidence) :
    P94ConformationEvidence.Supports
        (.ringPlane record : P94ConformationEvidence State Framework) .twist ↔
      record.unit.kind = .fiveMemberedRing ∧
        record.sides.length = record.unit.atoms.length ∧
        record.carbohydrateFiveRing ∧ IsCarbohydrateFiveRingTwist record.sides :=
  Iff.rfl

theorem p94TwistSupport_iff {State Framework : Type*} (record : P94TwistEvidence State) :
    P94ConformationEvidence.Supports
        (.twist record : P94ConformationEvidence State Framework) .twist ↔
      record.unit.kind = .sixMemberedRing ∧
        ExplicitTwistOnBoatInterconversion record.singleBondRotation
          record.endpointConformationsDistinct record.isBoatState record.isChairState record.candidate
          record.firstLeg record.secondLeg :=
  Iff.rfl

theorem p94HalfChairSupport_iff {State Framework : Type*} (record : P94HalfChairEvidence) :
    P94ConformationEvidence.Supports
        (.halfChair record : P94ConformationEvidence State Framework) .halfChair ↔
      record.unit.kind = .sixMemberedRing ∧ IsHalfChair record.observation :=
  Iff.rfl

/-- A molecule-admitted half-chair record has exactly one actual double bond in its named cyclic
traversal; the observation's numeric field cannot manufacture that premise. -/
theorem p94HalfChairSupport_implies_molecular_doubleBondCount_one
    {State Framework : Type*} (molecule : RawMolecule) (record : P94HalfChairEvidence)
    (roles : (P94ConformationEvidence.halfChair record :
      P94ConformationEvidence State Framework).MolecularRolesValid molecule)
    (support : P94ConformationEvidence.Supports
      (.halfChair record : P94ConformationEvidence State Framework) .halfChair) :
    record.unit.CycleDoubleBondCount molecule = 1 := by
  have observedOne : record.observation.doubleBondCount = 1 := support.2.2.1
  have observedActual : record.observation.doubleBondCount =
      record.unit.CycleDoubleBondCount molecule :=
    (P94HalfChairEvidence.molecularRolesValid_iff_doubleBondCount
      (State := State) (Framework := Framework) record molecule).mp roles |>.1
  omega

/-- A molecule-admitted half-chair is genuinely monounsaturated, not merely a ring whose numeric
ledger happens to contain one order-two entry alongside other unsaturation. -/
theorem p94HalfChairSupport_implies_molecular_monounsaturated
    {State Framework : Type*} (molecule : RawMolecule) (record : P94HalfChairEvidence)
    (roles : (P94ConformationEvidence.halfChair record :
      P94ConformationEvidence State Framework).MolecularRolesValid molecule) :
    record.unit.MonounsaturatedCyclic molecule :=
  (P94HalfChairEvidence.molecularRolesValid_iff_doubleBondCount
    (State := State) (Framework := Framework) record molecule).mp roles |>.2

theorem p94CrownSupport_iff {State Framework : Type*} (record : P94RingPlaneEvidence) :
    P94ConformationEvidence.Supports
        (.ringPlane record : P94ConformationEvidence State Framework) .crown ↔
      record.unit.kind = .crownRing ∧
        record.sides.length = record.unit.atoms.length ∧ record.saturatedCyclic ∧
        IsCrown record.sides record.symmetricallyEquivalent :=
  Iff.rfl

/-- A molecule-admitted crown record is saturated in the actual ring bond-order traversal. -/
theorem p94CrownSupport_implies_molecular_saturation
    {State Framework : Type*} (molecule : RawMolecule) (record : P94RingPlaneEvidence)
    (roles : (P94ConformationEvidence.ringPlane record :
      P94ConformationEvidence State Framework).MolecularRolesValid molecule)
    (support : P94ConformationEvidence.Supports
      (.ringPlane record : P94ConformationEvidence State Framework) .crown) :
    record.unit.SaturatedCyclic molecule :=
  (P94RingPlaneEvidence.molecularRolesValid_iff_crownSaturation
    (State := State) (Framework := Framework) record molecule support.1).mp roles

theorem p94TubSupport_iff {State Framework : Type*} (record : P94RingPlaneEvidence) :
    P94ConformationEvidence.Supports
        (.ringPlane record : P94ConformationEvidence State Framework) .tub ↔
      record.unit.kind = .eightMemberedTubRing ∧
        record.sides.length = record.unit.atoms.length ∧ IsTub record.sides :=
  Iff.rfl

theorem p94InOutSupport_iff {State Framework : Type*} (record : P94InOutEvidence Framework) :
    P94ConformationEvidence.Supports
        (.inOut record : P94ConformationEvidence State Framework) .inOut ↔
      record.unit.kind = .bicyclicBridge ∧ record.bicyclicSystem ∧
        AreInOutIsomers record.first record.second :=
  Iff.rfl

structure P94ConformationAssignment where
  unit : P94ConformationUnit
  descriptor : P94ConformationDescriptor
  deriving DecidableEq, Repr

def IndependentP94ConformationAssignment {State Framework : Type*}
    (molecule : RawMolecule) (evidence : List (P94ConformationEvidence State Framework))
    (assignment : P94ConformationAssignment) : Prop :=
  ∃ record ∈ evidence,
    record.unit = assignment.unit ∧
    assignment.unit.ValidFor molecule ∧
    record.MolecularRolesValid molecule ∧
    record.Supports assignment.descriptor

def P94ConformationEvidenceRefused {State Framework : Type*}
    (molecule : RawMolecule) (record : P94ConformationEvidence State Framework) : Prop :=
  ¬record.unit.ValidFor molecule ∨
    ¬record.MolecularRolesValid molecule ∨
    ¬∃ descriptor, record.Supports descriptor

private theorem mem_source_of_mem_eraseDups {α : Type*} [BEq α] [LawfulBEq α]
    (input : List α) (candidate : α) (present : candidate ∈ input.eraseDups) :
    candidate ∈ input := by
  match input with
  | [] => simp at present
  | head :: tail =>
      rw [List.eraseDups_cons] at present
      rcases List.mem_cons.mp present with atHead | inFiltered
      · exact List.mem_cons.mpr (.inl atHead)
      · have inFilter := mem_source_of_mem_eraseDups _ candidate inFiltered
        exact List.mem_cons.mpr (.inr (List.mem_filter.mp inFilter).1)
termination_by input.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

private theorem mem_eraseDups_of_mem {α : Type*} [BEq α] [LawfulBEq α]
    (input : List α) (candidate : α) (present : candidate ∈ input) :
    candidate ∈ input.eraseDups := by
  match input with
  | [] => simp at present
  | head :: tail =>
      rw [List.eraseDups_cons]
      rcases List.mem_cons.mp present with atHead | inTail
      · exact List.mem_cons.mpr (.inl atHead)
      · by_cases same : candidate = head
        · exact List.mem_cons.mpr (.inl same)
        · apply List.mem_cons.mpr
          apply Or.inr
          apply mem_eraseDups_of_mem
          exact List.mem_filter.mpr ⟨inTail, by simp [same]⟩
termination_by input.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

private theorem mem_eraseDups_iff_mem {α : Type*} [BEq α] [LawfulBEq α]
    (input : List α) (candidate : α) :
    candidate ∈ input.eraseDups ↔ candidate ∈ input :=
  ⟨mem_source_of_mem_eraseDups input candidate,
    mem_eraseDups_of_mem input candidate⟩

private theorem eraseDups_nodup {α : Type*} [BEq α] [LawfulBEq α]
    (input : List α) : input.eraseDups.Nodup := by
  match input with
  | [] => simp
  | head :: tail =>
      rw [List.eraseDups_cons]
      apply List.nodup_cons.mpr
      refine ⟨?_, eraseDups_nodup _⟩
      rw [mem_eraseDups_iff_mem]
      simp
termination_by input.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

private def p94ConformationCandidates {State Framework : Type*}
    (evidence : List (P94ConformationEvidence State Framework)) :
    List P94ConformationAssignment :=
  (evidence.flatMap fun record =>
    P94ConformationDescriptor.all.map fun descriptor =>
      { unit := record.unit, descriptor := descriptor }).eraseDups

private theorem mem_p94ConformationCandidates_iff {State Framework : Type*}
    (evidence : List (P94ConformationEvidence State Framework))
    (assignment : P94ConformationAssignment) :
    assignment ∈ p94ConformationCandidates evidence ↔
      ∃ record ∈ evidence, record.unit = assignment.unit := by
  classical
  rw [p94ConformationCandidates, mem_eraseDups_iff_mem, List.mem_flatMap]
  constructor
  · rintro ⟨record, recordPresent, assignmentPresent⟩
    rcases List.mem_map.mp assignmentPresent with ⟨descriptor, _, assignmentEq⟩
    exact ⟨record, recordPresent, by cases assignmentEq; rfl⟩
  · rintro ⟨record, recordPresent, unitEq⟩
    refine ⟨record, recordPresent, List.mem_map.mpr ?_⟩
    exact ⟨assignment.descriptor, P94ConformationDescriptor.mem_all _, by
      cases assignment
      simp_all⟩

/-- The complete P-94 report on the exact molecule carried by the reviewed observation.
Candidate erasure is only a multiplicity policy; the filter is exactly the independent relation
above.  P-94 conformation assignment does not require whole-chemistry normalization. -/
noncomputable def RawMolecule.analyzeP94Conformation
    {State Framework : Type*} (molecule : RawMolecule)
    (evidence : List (P94ConformationEvidence State Framework)) :
    List P94ConformationAssignment := by
  classical
  exact (p94ConformationCandidates evidence).filter fun assignment =>
    decide (IndependentP94ConformationAssignment molecule evidence assignment)

theorem RawMolecule.mem_analyzeP94Conformation_iff_independent {State Framework : Type*}
    (molecule : RawMolecule)
    (evidence : List (P94ConformationEvidence State Framework))
    (assignment : P94ConformationAssignment) :
    assignment ∈ molecule.analyzeP94Conformation evidence ↔
      IndependentP94ConformationAssignment molecule evidence assignment := by
  classical
  rw [RawMolecule.analyzeP94Conformation, List.mem_filter, decide_eq_true_eq]
  constructor
  · exact fun present => present.2
  · intro independent
    refine ⟨(mem_p94ConformationCandidates_iff evidence assignment).mpr ?_, independent⟩
    rcases independent with ⟨record, recordPresent, unitEq, _⟩
    exact ⟨record, recordPresent, unitEq⟩

/-- Compatibility wrapper for callers that already possess a certified whole-chemistry
normalization result. -/
noncomputable def CertifiedChemistryNormalizationResult.analyzeP94Conformation
    {State Framework : Type*} (certified : CertifiedChemistryNormalizationResult)
    (evidence : List (P94ConformationEvidence State Framework)) :
    List P94ConformationAssignment :=
  certified.result.parsed.analyzeP94Conformation evidence

theorem mem_analyzeP94Conformation_iff_independent {State Framework : Type*}
    (certified : CertifiedChemistryNormalizationResult)
    (evidence : List (P94ConformationEvidence State Framework))
    (assignment : P94ConformationAssignment) :
    assignment ∈ certified.analyzeP94Conformation evidence ↔
      IndependentP94ConformationAssignment certified.result.parsed evidence assignment :=
  RawMolecule.mem_analyzeP94Conformation_iff_independent
    certified.result.parsed evidence assignment

theorem analyzeP94Conformation_member_sound {State Framework : Type*}
    (certified : CertifiedChemistryNormalizationResult)
    (evidence : List (P94ConformationEvidence State Framework))
    (assignment : P94ConformationAssignment)
    (present : assignment ∈ certified.analyzeP94Conformation evidence) :
    IndependentP94ConformationAssignment certified.result.parsed evidence assignment :=
  (mem_analyzeP94Conformation_iff_independent certified evidence assignment).mp present

theorem analyzeP94Conformation_nodup {State Framework : Type*}
    (certified : CertifiedChemistryNormalizationResult)
    (evidence : List (P94ConformationEvidence State Framework)) :
    (certified.analyzeP94Conformation evidence).Nodup := by
  classical
  unfold CertifiedChemistryNormalizationResult.analyzeP94Conformation
  unfold RawMolecule.analyzeP94Conformation
  apply List.Nodup.filter
  unfold p94ConformationCandidates
  exact eraseDups_nodup _

theorem analyzeP94Conformation_count_eq_one_iff {State Framework : Type*}
    (certified : CertifiedChemistryNormalizationResult)
    (evidence : List (P94ConformationEvidence State Framework))
    (assignment : P94ConformationAssignment) :
    List.count assignment (certified.analyzeP94Conformation evidence) = 1 ↔
      IndependentP94ConformationAssignment certified.result.parsed evidence assignment := by
  classical
  constructor
  · intro countOne
    apply (mem_analyzeP94Conformation_iff_independent certified evidence assignment).mp
    by_contra absent
    have countZero : List.count assignment (certified.analyzeP94Conformation evidence) = 0 :=
      List.count_eq_zero_of_not_mem absent
    omega
  · intro independent
    exact List.count_eq_one_of_mem
      (analyzeP94Conformation_nodup certified evidence)
      ((mem_analyzeP94Conformation_iff_independent certified evidence assignment).mpr independent)

theorem analyzeP94Conformation_count_eq_zero_iff {State Framework : Type*}
    (certified : CertifiedChemistryNormalizationResult)
    (evidence : List (P94ConformationEvidence State Framework))
    (assignment : P94ConformationAssignment) :
    List.count assignment (certified.analyzeP94Conformation evidence) = 0 ↔
      ¬IndependentP94ConformationAssignment certified.result.parsed evidence assignment := by
  classical
  rw [List.count_eq_zero, mem_analyzeP94Conformation_iff_independent]

theorem p94ConformationEvidence_not_refused_iff {State Framework : Type*}
    (molecule : RawMolecule) (record : P94ConformationEvidence State Framework) :
    ¬P94ConformationEvidenceRefused molecule record ↔
      record.unit.ValidFor molecule ∧
      record.MolecularRolesValid molecule ∧
      ∃ descriptor, record.Supports descriptor := by
  simp [P94ConformationEvidenceRefused]

/-- Every independently supported descriptor is retained, including both adjacent classes at an
inclusive P-94 torsion boundary. -/
theorem analyzeP94Conformation_emits_every_supported {State Framework : Type*}
    (certified : CertifiedChemistryNormalizationResult)
    (evidence : List (P94ConformationEvidence State Framework))
    (record : P94ConformationEvidence State Framework) (recordPresent : record ∈ evidence)
    (valid : record.unit.ValidFor certified.result.parsed)
    (rolesValid : record.MolecularRolesValid certified.result.parsed)
    (descriptor : P94ConformationDescriptor) (support : record.Supports descriptor) :
    ({ unit := record.unit, descriptor := descriptor } : P94ConformationAssignment) ∈
      certified.analyzeP94Conformation evidence := by
  apply (mem_analyzeP94Conformation_iff_independent certified evidence _).mpr
  exact ⟨record, recordPresent, rfl, valid, rolesValid, support⟩

/-- P-94's inclusive interval wording is observed literally: an exact 30° torsion emits both
`synperiplanar` and `synclinal`, never an implementation-selected single winner. -/
theorem p94ThirtyDegreeBoundary_emits_both {State Framework : Type*}
    (certified : CertifiedChemistryNormalizationResult)
    (evidence : List (P94ConformationEvidence State Framework))
    (record : P94TorsionEvidence)
    (recordPresent : (P94ConformationEvidence.torsion record :
      P94ConformationEvidence State Framework) ∈ evidence)
    (valid : record.unit.ValidFor certified.result.parsed)
    (rolesValid :
      (P94ConformationEvidence.torsion record : P94ConformationEvidence State Framework).MolecularRolesValid
        certified.result.parsed)
    (torsionKind : record.unit.kind = .torsionAxis)
    (selected : record.SelectedBySourceCriteria)
    (degrees : record.frame.angle.degrees = 30) :
    ({ unit := record.unit, descriptor := .torsionClass .synperiplanar } :
        P94ConformationAssignment) ∈ certified.analyzeP94Conformation evidence ∧
      ({ unit := record.unit, descriptor := .torsionClass .synclinal } :
        P94ConformationAssignment) ∈ certified.analyzeP94Conformation evidence := by
  have magnitude : record.frame.angle.magnitude = 30 := by
    simp [TorsionAngle.magnitude, degrees]
  have synperiplanar : ClassifiedAs record.frame.angle .synperiplanar := by
    norm_num [ClassifiedAs, magnitude]
  have synclinal : ClassifiedAs record.frame.angle .synclinal := by
    norm_num [ClassifiedAs, magnitude]
  constructor
  · exact analyzeP94Conformation_emits_every_supported certified evidence
      (.torsion record) recordPresent valid rolesValid _
      ⟨torsionKind, selected, synperiplanar⟩
  · exact analyzeP94Conformation_emits_every_supported certified evidence
      (.torsion record) recordPresent valid rolesValid _
      ⟨torsionKind, selected, synclinal⟩

theorem p94ConformationEvidence_exhaustive {State Framework : Type*}
    (certified : CertifiedChemistryNormalizationResult)
    (evidence : List (P94ConformationEvidence State Framework))
    (record : P94ConformationEvidence State Framework) (recordPresent : record ∈ evidence) :
    (∃ descriptor,
      record.Supports descriptor ∧
      ({ unit := record.unit, descriptor := descriptor } : P94ConformationAssignment) ∈
        certified.analyzeP94Conformation evidence) ∨
      P94ConformationEvidenceRefused certified.result.parsed record := by
  by_cases valid : record.unit.ValidFor certified.result.parsed
  · by_cases rolesValid : record.MolecularRolesValid certified.result.parsed
    · by_cases supported : ∃ descriptor, record.Supports descriptor
      · rcases supported with ⟨descriptor, support⟩
        exact .inl ⟨descriptor, support,
          analyzeP94Conformation_emits_every_supported certified evidence record recordPresent
            valid rolesValid descriptor support⟩
      · exact .inr (.inr (.inr supported))
    · exact .inr (.inr (.inl rolesValid))
  · exact .inr (.inl valid)

end TetraStereo.OneCenter
