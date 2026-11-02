import TetraStereo.OneCenter.P94CoordinateRingConformation
import TetraStereo.OneCenter.P94MoleculeCoordinateTorsion

set_option autoImplicit false

namespace TetraStereo.OneCenter

open BlueBookP94

/-!
# Exact P-94 twist and in-out perception

This module closes the two represented P-94.3.2 families which cannot be recognized from a
single ring-side ledger.

A twist is not merely any member of the rotation-equivalence component containing two boats.
It must occur strictly between two coordinate-distinct, coordinate-derived boat states on one
finite path of direct formally-single-bond rotations, and the candidate itself must be neither a
boat nor a chair.  Nuclear coordinates do not say which formal single bond was rotated between
two complete states, so that unoriented direct-step relation is retained as an explicit independent
premise and is bounded to the finite state ledger.

For in-out isomerism, exact rational coordinates determine whether an exocyclic atom or explicit
lone-pair point is directed toward or away from an independently validated framework-interior
point.  The present raw molecule does not perceive a general bicyclic framework, bridge length,
framework identity, lone-pair inventory, or a canonical cage interior.  Those facts are therefore
named by `IndependentInOutPremises`, including full-framework atom membership; they are not
guessed from a path-shaped carrier.  Relative to that honest boundary, positive results, all
refusals, and public exact-once emission are complete.
-/

namespace BlueBookP94.CoordinateTwistInOut

/-! ## A functional specification selector -/

private noncomputable def specificationChoice? {Alpha : Type*}
    (predicate : Alpha → Prop) : Option Alpha := by
  classical
  exact if present : ∃ value, predicate value then
    some (Classical.choose present)
  else
    none

private theorem specificationChoice?_eq_some_iff {Alpha : Type*}
    (predicate : Alpha → Prop)
    (functional : ∀ left right, predicate left → predicate right → left = right)
    (value : Alpha) :
    specificationChoice? predicate = some value ↔ predicate value := by
  classical
  by_cases present : ∃ candidate, predicate candidate
  · have chosen : predicate (Classical.choose present) := Classical.choose_spec present
    constructor
    · intro computed
      have equal : Classical.choose present = value := by
        simpa [specificationChoice?, present] using computed
      simpa [← equal] using chosen
    · intro judged
      have equal := functional (Classical.choose present) value chosen judged
      simp [specificationChoice?, present, equal]
  · constructor
    · intro computed
      simp [specificationChoice?, present] at computed
    · intro judged
      exact False.elim (present ⟨value, judged⟩)

private theorem specificationChoice?_eq_none_iff {Alpha : Type*}
    (predicate : Alpha → Prop) :
    specificationChoice? predicate = none ↔ ¬∃ value, predicate value := by
  classical
  by_cases present : ∃ value, predicate value <;>
    simp [specificationChoice?, present]

/-! ## A genuine finite boat-to-boat twist path -/

/-- The coordinate layer uses the authoritative ordered-path object from the independent P-94
specification directly; these aliases preserve the public namespace introduced by this module. -/
abbrev DirectedRotationPath {State : Type*}
    (singleBondRotation : State → State → Prop) : List State → Prop :=
  BlueBookP94.DirectedRotationPath singleBondRotation

abbrev ExplicitTwistOnBoatInterconversion {State : Type*}
    (singleBondRotation : State → State → Prop)
    (endpointConformationsDistinct : State → State → Prop)
    (isBoatState isChairState : State → Prop) (candidate : State)
    (firstLeg secondLeg : List State) : Prop :=
  BlueBookP94.ExplicitTwistOnBoatInterconversion singleBondRotation
    endpointConformationsDistinct isBoatState isChairState candidate firstLeg secondLeg

/-- The strong path relation entails the older equivalence-component relation.  The converse is
not used: equivalence closure forgets path order and cannot establish that the candidate was an
interior non-chair state. -/
theorem explicitTwistOnBoatInterconversion_implies_weak {State : Type*}
    {singleBondRotation : State → State → Prop}
    {endpointConformationsDistinct : State → State → Prop}
    {isBoatState isChairState : State → Prop} {candidate : State}
    {firstLeg secondLeg : List State}
    (explicit : ExplicitTwistOnBoatInterconversion singleBondRotation
      endpointConformationsDistinct isBoatState isChairState candidate firstLeg secondLeg) :
    IsTwistOnBoatInterconversion singleBondRotation isBoatState candidate :=
  BlueBookP94.explicitTwistOnBoatInterconversion_implies_weak explicit

theorem explicitTwistOnBoatInterconversion_candidate_not_boat {State : Type*}
    {singleBondRotation : State → State → Prop}
    {endpointConformationsDistinct : State → State → Prop}
    {isBoatState isChairState : State → Prop} {candidate : State}
    {firstLeg secondLeg : List State}
    (explicit : ExplicitTwistOnBoatInterconversion singleBondRotation
      endpointConformationsDistinct isBoatState isChairState candidate firstLeg secondLeg) :
    ¬isBoatState candidate := by
  rcases explicit with ⟨_, _, _, _, _, _, candidateNotBoat, _⟩
  exact candidateNotBoat

theorem explicitTwistOnBoatInterconversion_candidate_not_chair {State : Type*}
    {singleBondRotation : State → State → Prop}
    {endpointConformationsDistinct : State → State → Prop}
    {isBoatState isChairState : State → Prop} {candidate : State}
    {firstLeg secondLeg : List State}
    (explicit : ExplicitTwistOnBoatInterconversion singleBondRotation
      endpointConformationsDistinct isBoatState isChairState candidate firstLeg secondLeg) :
    ¬isChairState candidate := by
  rcases explicit with ⟨_, _, _, _, _, _, _, candidateNotChair, _⟩
  exact candidateNotChair

/-- With a universal step relation, the old equivalence-component predicate accepts literally
any candidate state.  It therefore contains no evidence that the candidate occurs at the twist
position of a particular finite boat-to-boat path. -/
theorem weakTwist_accepts_arbitrary_candidate_of_universal_rotation {State : Type*}
    (firstBoat secondBoat candidate : State) (distinct : firstBoat ≠ secondBoat) :
    IsTwistOnBoatInterconversion (fun _ _ : State => True)
      (fun state => state = firstBoat ∨ state = secondBoat) candidate := by
  exact ⟨firstBoat, secondBoat, distinct, Or.inl rfl, Or.inr rfl,
    .step trivial, .step trivial⟩

/-- Concrete strictness witness for the semantic repair: the old predicate accepts state `1`
even when an independent chair predicate classifies it as a chair, whereas no strong explicit
twist path can accept it. -/
theorem weakTwist_does_not_imply_explicit_counterexample :
    let rotation : Fin 3 → Fin 3 → Prop := fun _ _ => True
    let boat : Fin 3 → Prop := fun state => state = 0 ∨ state = 2
    let chair : Fin 3 → Prop := fun state => state = 1
    let candidate : Fin 3 := 1
    IsTwistOnBoatInterconversion rotation boat candidate ∧
      ∀ firstLeg secondLeg,
        ¬ExplicitTwistOnBoatInterconversion rotation (· ≠ ·) boat chair candidate
          firstLeg secondLeg := by
  dsimp
  constructor
  · exact weakTwist_accepts_arbitrary_candidate_of_universal_rotation
      (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (by decide)
  · intro firstLeg secondLeg explicit
    exact (explicitTwistOnBoatInterconversion_candidate_not_chair explicit) rfl

/-- Finite complete-state ledger for one proposed twist path.  `independentSingleBondRotation`
means a direct rotation about one formal single bond; it is explicit because this fact cannot be
reconstructed from two coordinate snapshots alone.  Path semantics symmetrize each asserted edge,
so this relation may consistently orient its ledger in either direction. -/
structure CoordinateTwistInput (State : Type*) where
  unit : P94ConformationUnit
  states : List State
  spatialAt : State → SpatialConfiguration
  independentSingleBondRotation : State → State → Prop
  candidate : State
  firstLeg : List State
  secondLeg : List State

def CoordinateTwistInput.BoundedSingleBondRotation {State : Type*}
    [DecidableEq State] (input : CoordinateTwistInput State)
    (first second : State) : Prop :=
  first ∈ input.states ∧ second ∈ input.states ∧
    input.independentSingleBondRotation first second

-- Retain the molecule argument in these public predicates to keep the carrier interface explicit.
set_option linter.unusedVariables false in
/-- A ledger state is a boat exactly when some exact ring-spanned plane gives the printed boat
pattern.  The plane is existential rather than a caller-selected privileged drawing plane. -/
def CoordinateBoatState {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (input : CoordinateTwistInput State) (state : State) : Prop :=
  state ∈ input.states ∧
    ∃ plane sides,
      CoordinateRing.RingSidesOfPlane (input.spatialAt state) input.unit.atoms plane sides ∧
      IsBoat sides

set_option linter.unusedVariables false in
/-- Coordinate chair recognition over the same exact molecule-bound ring carrier. -/
def CoordinateChairState {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (input : CoordinateTwistInput State) (state : State) : Prop :=
  state ∈ input.states ∧
    ∃ plane sides,
      CoordinateRing.RingSidesOfPlane (input.spatialAt state) input.unit.atoms plane sides ∧
      IsChair sides

abbrev CoordinateTwistEvidence (State : Type*) :=
  P94ConformationEvidence State Unit

private def coordinateTwistRecord {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (input : CoordinateTwistInput State) :
    CoordinateTwistEvidence State :=
  .twist
    { unit := input.unit
      singleBondRotation := input.BoundedSingleBondRotation
      endpointConformationsDistinct := fun first second =>
        input.spatialAt first ≠ input.spatialAt second
      isBoatState := CoordinateBoatState molecule input
      isChairState := CoordinateChairState molecule input
      candidate := input.candidate
      firstLeg := input.firstLeg
      secondLeg := input.secondLeg }

/-- Independent exact meaning of a successful finite coordinate twist derivation. -/
def CoordinateTwistEvidenceJudgment {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (input : CoordinateTwistInput State)
    (output : CoordinateTwistEvidence State) : Prop :=
  input.unit.kind = .sixMemberedRing ∧
    input.unit.ValidFor molecule ∧
    input.states.Nodup ∧
    (∀ state ∈ input.firstLeg ++ input.secondLeg.tail, state ∈ input.states) ∧
    ExplicitTwistOnBoatInterconversion input.BoundedSingleBondRotation
      (fun first second => input.spatialAt first ≠ input.spatialAt second)
      (CoordinateBoatState molecule input) (CoordinateChairState molecule input)
      input.candidate input.firstLeg input.secondLeg ∧
    output = coordinateTwistRecord molecule input

private theorem coordinateTwistEvidenceJudgment_functional {State : Type*}
    [DecidableEq State] (molecule : RawMolecule) (input : CoordinateTwistInput State) :
    ∀ left right,
      CoordinateTwistEvidenceJudgment molecule input left →
      CoordinateTwistEvidenceJudgment molecule input right → left = right := by
  rintro left right ⟨_, _, _, _, _, rfl⟩ ⟨_, _, _, _, _, rfl⟩
  rfl

noncomputable def coordinateTwistEvidence? {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (input : CoordinateTwistInput State) :
    Option (CoordinateTwistEvidence State) :=
  specificationChoice? (CoordinateTwistEvidenceJudgment molecule input)

theorem coordinateTwistEvidence?_eq_some_iff {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (input : CoordinateTwistInput State)
    (output : CoordinateTwistEvidence State) :
    coordinateTwistEvidence? molecule input = some output ↔
      CoordinateTwistEvidenceJudgment molecule input output :=
  specificationChoice?_eq_some_iff _
    (coordinateTwistEvidenceJudgment_functional molecule input) output

theorem coordinateTwistEvidence?_eq_none_iff {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (input : CoordinateTwistInput State) :
    coordinateTwistEvidence? molecule input = none ↔
      ¬∃ output, CoordinateTwistEvidenceJudgment molecule input output :=
  specificationChoice?_eq_none_iff _

theorem coordinateTwistEvidenceJudgment_supports_twist {State : Type*}
    [DecidableEq State] (molecule : RawMolecule) (input : CoordinateTwistInput State)
    (output : CoordinateTwistEvidence State)
    (judged : CoordinateTwistEvidenceJudgment molecule input output) :
    output.unit.ValidFor molecule ∧
      output.MolecularRolesValid molecule ∧
      output.Supports .twist := by
  rcases judged with ⟨kind, valid, ledgerNodup, bounded, explicit, rfl⟩
  refine ⟨valid, ?_, kind, ?_⟩
  · simp [coordinateTwistRecord, P94ConformationEvidence.MolecularRolesValid]
  · exact explicit

/-- Every successful coordinate judgment contains two boat endpoints whose complete spatial
configurations differ, rather than merely two different ledger identifiers. -/
theorem coordinateTwistEvidenceJudgment_has_spatially_distinct_boats {State : Type*}
    [DecidableEq State] (molecule : RawMolecule) (input : CoordinateTwistInput State)
    (output : CoordinateTwistEvidence State)
    (judged : CoordinateTwistEvidenceJudgment molecule input output) :
    ∃ firstBoat secondBoat,
      CoordinateBoatState molecule input firstBoat ∧
      CoordinateBoatState molecule input secondBoat ∧
      input.spatialAt firstBoat ≠ input.spatialAt secondBoat := by
  rcases judged with ⟨_, _, _, _, explicit, _⟩
  rcases explicit with
    ⟨firstBoat, secondBoat, _stateDistinct, spatiallyDistinct,
      firstBoatIsBoat, secondBoatIsBoat, _⟩
  exact ⟨firstBoat, secondBoat, firstBoatIsBoat, secondBoatIsBoat, spatiallyDistinct⟩

/-! ## Exact coordinate direction for in-out isomerism -/

/-- Chemical facts required by P-94.3.2.6 but not present in the current raw-molecule carrier.
`AtomInFramework` describes the complete independently perceived bicyclic framework, not only
the atoms of the named conformation unit.  `BridgeheadInFramework` is deliberately separate:
being any framework atom is not sufficient for an in/out site.  The interior witness is indexed
by that bridgehead so an observation cannot silently reuse an interior reference chosen for a
different endpoint.  Keeping framework, bridge-length, interior, membership, and electron facts
as relations makes their authority boundary visible and replaceable by proved perception layers. -/
structure IndependentInOutPremises (Framework : Type*) where
  BicyclicFramework : RawMolecule → P94ConformationUnit → Framework → Prop
  BridgeLongEnough : RawMolecule → P94ConformationUnit → Framework → Prop
  InteriorWitness : RawMolecule → P94ConformationUnit → Framework →
    ℕ → SpatialConfiguration → CartesianPoint3 → Prop
  AtomInFramework : RawMolecule → P94ConformationUnit → Framework → ℕ → Prop
  BridgeheadInFramework : RawMolecule → P94ConformationUnit → Framework → ℕ → Prop
  LonePairAt : RawMolecule → ℕ → Prop

/-- One of the two finite framework observations.  Direction is deliberately absent: it will be
derived from the coordinate alignment with `interior`. -/
structure CoordinateInOutObservation (Framework : Type*) where
  framework : Framework
  spatial : SpatialConfiguration
  virtualPoints : CoordinateTorsion.VirtualTorsionPointLedger
  bridgehead : ℕ
  directedParticipant : TorsionParticipant ℕ
  interior : CartesianPoint3

/-- The directed participant is either an actual bonded atom proved outside the complete bicyclic
framework or an explicitly admitted lone pair on its bridgehead.  Multiple-bond duplicates are
not P-94.3.2.6 directional sites. -/
def InOutParticipantChemicallyValid {Framework : Type*}
    (premises : IndependentInOutPremises Framework) (molecule : RawMolecule)
    (unit : P94ConformationUnit) (framework : Framework) (bridgehead : ℕ) :
    TorsionParticipant ℕ → Prop
  | .atom atom =>
      bridgehead ∈ unit.atoms ∧
      premises.BridgeheadInFramework molecule unit framework bridgehead ∧
      bridgehead < molecule.atomCount ∧ atom < molecule.atomCount ∧
      atom ∉ unit.atoms ∧ ¬premises.AtomInFramework molecule unit framework atom ∧
      0 < molecule.bondOrder bridgehead atom
  | .lonePair center =>
      bridgehead ∈ unit.atoms ∧
      premises.BridgeheadInFramework molecule unit framework bridgehead ∧
      bridgehead < molecule.atomCount ∧
      center = bridgehead ∧ premises.LonePairAt molecule bridgehead
  | .duplicateAtom _ => False

/-- Every chemically admitted in/out participant is attached to an independently certified
bridgehead, not merely to an arbitrary atom of the framework. -/
theorem inOutParticipantChemicallyValid_bridgeheadInFramework {Framework : Type*}
    (premises : IndependentInOutPremises Framework) (molecule : RawMolecule)
    (unit : P94ConformationUnit) (framework : Framework) (bridgehead : ℕ)
    (participant : TorsionParticipant ℕ)
    (valid : InOutParticipantChemicallyValid premises molecule unit framework bridgehead
      participant) :
    premises.BridgeheadInFramework molecule unit framework bridgehead := by
  cases participant <;> simp_all [InOutParticipantChemicallyValid]

theorem inOutParticipantChemicallyValid_atom_outside_framework {Framework : Type*}
    (premises : IndependentInOutPremises Framework) (molecule : RawMolecule)
    (unit : P94ConformationUnit) (framework : Framework) (bridgehead atom : ℕ)
    (valid : InOutParticipantChemicallyValid premises molecule unit framework bridgehead
      (.atom atom)) :
    ¬premises.AtomInFramework molecule unit framework atom := by
  rcases valid with ⟨_, _, _, _, _, outsideFramework, _⟩
  exact outsideFramework

/-- Exact independent coordinate meaning of one inward/outward label.  Positive alignment with
the validated bridgehead-to-interior direction is inward; negative alignment is outward; a zero
alignment is refused. -/
def CoordinateInOutDirectionJudgment {Framework : Type*}
    (premises : IndependentInOutPremises Framework) (molecule : RawMolecule)
    (unit : P94ConformationUnit) (observation : CoordinateInOutObservation Framework)
    (direction : BridgeheadDirection) : Prop :=
  observation.virtualPoints.Valid ∧
    premises.InteriorWitness molecule unit observation.framework
      observation.bridgehead observation.spatial observation.interior ∧
    InOutParticipantChemicallyValid premises molecule unit observation.framework
      observation.bridgehead
      observation.directedParticipant ∧
    ∃ bridgeheadPoint participantPoint,
      CoordinateRing.SpatialPointAt observation.spatial observation.bridgehead bridgeheadPoint ∧
      CoordinateTorsion.ParticipantPointAt observation.spatial observation.virtualPoints
        observation.directedParticipant participantPoint ∧
      let alignment := RationalVector3.dot
        (CartesianPoint3.displacement bridgeheadPoint participantPoint)
        (CartesianPoint3.displacement bridgeheadPoint observation.interior)
      match direction with
      | .inward => 0 < alignment
      | .outward => alignment < 0

private theorem coordinateInOutDirectionJudgment_functional {Framework : Type*}
    (premises : IndependentInOutPremises Framework) (molecule : RawMolecule)
    (unit : P94ConformationUnit) (observation : CoordinateInOutObservation Framework) :
    ∀ left right,
      CoordinateInOutDirectionJudgment premises molecule unit observation left →
      CoordinateInOutDirectionJudgment premises molecule unit observation right →
      left = right := by
  rintro left right
    ⟨leftLedgerValid, _, _, leftBridgePoint, leftParticipantPoint,
      leftBridgeAt, leftParticipantAt, leftSign⟩
    ⟨rightLedgerValid, _, _, rightBridgePoint, rightParticipantPoint,
      rightBridgeAt, rightParticipantAt, rightSign⟩
  have bridgeEqual : leftBridgePoint = rightBridgePoint := by
    unfold CoordinateRing.SpatialPointAt at leftBridgeAt rightBridgeAt
    rw [leftBridgeAt] at rightBridgeAt
    exact Option.some.inj rightBridgeAt
  have leftLookup := (CoordinateTorsion.participantPoint?_eq_some_iff
    observation.spatial observation.virtualPoints leftLedgerValid
    observation.directedParticipant leftParticipantPoint).mpr leftParticipantAt
  have rightLookup := (CoordinateTorsion.participantPoint?_eq_some_iff
    observation.spatial observation.virtualPoints rightLedgerValid
    observation.directedParticipant rightParticipantPoint).mpr rightParticipantAt
  rw [leftLookup] at rightLookup
  have participantEqual : leftParticipantPoint = rightParticipantPoint :=
    Option.some.inj rightLookup
  subst rightBridgePoint
  subst rightParticipantPoint
  cases left <;> cases right
  · rfl
  · exfalso
    exact (not_lt_of_ge leftSign.le) rightSign
  · exfalso
    exact (not_lt_of_ge rightSign.le) leftSign
  · rfl

noncomputable def coordinateInOutDirection? {Framework : Type*}
    (premises : IndependentInOutPremises Framework) (molecule : RawMolecule)
    (unit : P94ConformationUnit) (observation : CoordinateInOutObservation Framework) :
    Option BridgeheadDirection :=
  specificationChoice? (CoordinateInOutDirectionJudgment premises molecule unit observation)

theorem coordinateInOutDirection?_eq_some_iff {Framework : Type*}
    (premises : IndependentInOutPremises Framework) (molecule : RawMolecule)
    (unit : P94ConformationUnit) (observation : CoordinateInOutObservation Framework)
    (direction : BridgeheadDirection) :
    coordinateInOutDirection? premises molecule unit observation = some direction ↔
      CoordinateInOutDirectionJudgment premises molecule unit observation direction :=
  specificationChoice?_eq_some_iff _
    (coordinateInOutDirectionJudgment_functional premises molecule unit observation) direction

theorem coordinateInOutDirection?_eq_none_iff {Framework : Type*}
    (premises : IndependentInOutPremises Framework) (molecule : RawMolecule)
    (unit : P94ConformationUnit) (observation : CoordinateInOutObservation Framework) :
    coordinateInOutDirection? premises molecule unit observation = none ↔
      ¬∃ direction,
        CoordinateInOutDirectionJudgment premises molecule unit observation direction :=
  specificationChoice?_eq_none_iff _

structure CoordinateInOutInput (Framework : Type*) where
  unit : P94ConformationUnit
  first : CoordinateInOutObservation Framework
  second : CoordinateInOutObservation Framework

abbrev CoordinateInOutEvidence (Framework : Type*) :=
  P94ConformationEvidence Unit Framework

private def coordinateInOutRecord {Framework : Type*}
    (premises : IndependentInOutPremises Framework) (molecule : RawMolecule)
    (input : CoordinateInOutInput Framework)
    (firstDirection secondDirection : BridgeheadDirection) :
    CoordinateInOutEvidence Framework :=
  .inOut
    { unit := input.unit
      first :=
        { framework := input.first.framework
          bridgehead := input.first.bridgehead
          directedParticipant := input.first.directedParticipant
          bridgeLongEnough := premises.BridgeLongEnough molecule input.unit input.first.framework
          direction := firstDirection }
      second :=
        { framework := input.second.framework
          bridgehead := input.second.bridgehead
          directedParticipant := input.second.directedParticipant
          bridgeLongEnough := premises.BridgeLongEnough molecule input.unit input.second.framework
          direction := secondDirection }
      bicyclicSystem :=
        premises.BicyclicFramework molecule input.unit input.first.framework }

/-- Independent exact meaning of a successful pair of coordinate framework observations. -/
def CoordinateInOutEvidenceJudgment {Framework : Type*}
    (premises : IndependentInOutPremises Framework) (molecule : RawMolecule)
    (input : CoordinateInOutInput Framework) (output : CoordinateInOutEvidence Framework) : Prop :=
  input.unit.kind = .bicyclicBridge ∧
    input.unit.ValidFor molecule ∧
    premises.BicyclicFramework molecule input.unit input.first.framework ∧
    input.first.framework = input.second.framework ∧
    input.first.bridgehead = input.second.bridgehead ∧
    input.first.directedParticipant = input.second.directedParticipant ∧
    premises.BridgeLongEnough molecule input.unit input.first.framework ∧
    premises.BridgeLongEnough molecule input.unit input.second.framework ∧
    ∃ firstDirection secondDirection,
      CoordinateInOutDirectionJudgment premises molecule input.unit input.first firstDirection ∧
      CoordinateInOutDirectionJudgment premises molecule input.unit input.second secondDirection ∧
      firstDirection ≠ secondDirection ∧
      output = coordinateInOutRecord premises molecule input firstDirection secondDirection

private theorem coordinateInOutEvidenceJudgment_functional {Framework : Type*}
    (premises : IndependentInOutPremises Framework) (molecule : RawMolecule)
    (input : CoordinateInOutInput Framework) :
    ∀ left right,
      CoordinateInOutEvidenceJudgment premises molecule input left →
      CoordinateInOutEvidenceJudgment premises molecule input right → left = right := by
  rintro left right
    ⟨_, _, _, _, _, _, _, _, leftDirection, leftOtherDirection,
      leftJudged, leftOtherJudged, _, rfl⟩
    ⟨_, _, _, _, _, _, _, _, rightDirection, rightOtherDirection,
      rightJudged, rightOtherJudged, _, rfl⟩
  have firstEqual := coordinateInOutDirectionJudgment_functional
    premises molecule input.unit input.first
    leftDirection rightDirection leftJudged rightJudged
  have secondEqual := coordinateInOutDirectionJudgment_functional
    premises molecule input.unit input.second
    leftOtherDirection rightOtherDirection leftOtherJudged rightOtherJudged
  subst rightDirection
  subst rightOtherDirection
  rfl

noncomputable def coordinateInOutEvidence? {Framework : Type*}
    (premises : IndependentInOutPremises Framework) (molecule : RawMolecule)
    (input : CoordinateInOutInput Framework) : Option (CoordinateInOutEvidence Framework) :=
  specificationChoice? (CoordinateInOutEvidenceJudgment premises molecule input)

theorem coordinateInOutEvidence?_eq_some_iff {Framework : Type*}
    (premises : IndependentInOutPremises Framework) (molecule : RawMolecule)
    (input : CoordinateInOutInput Framework) (output : CoordinateInOutEvidence Framework) :
    coordinateInOutEvidence? premises molecule input = some output ↔
      CoordinateInOutEvidenceJudgment premises molecule input output :=
  specificationChoice?_eq_some_iff _
    (coordinateInOutEvidenceJudgment_functional premises molecule input) output

theorem coordinateInOutEvidence?_eq_none_iff {Framework : Type*}
    (premises : IndependentInOutPremises Framework) (molecule : RawMolecule)
    (input : CoordinateInOutInput Framework) :
    coordinateInOutEvidence? premises molecule input = none ↔
      ¬∃ output, CoordinateInOutEvidenceJudgment premises molecule input output :=
  specificationChoice?_eq_none_iff _

theorem coordinateInOutEvidenceJudgment_supports_inOut {Framework : Type*}
    (premises : IndependentInOutPremises Framework) (molecule : RawMolecule)
    (input : CoordinateInOutInput Framework) (output : CoordinateInOutEvidence Framework)
    (judged : CoordinateInOutEvidenceJudgment premises molecule input output) :
    output.unit.ValidFor molecule ∧
      output.MolecularRolesValid molecule ∧
      output.Supports .inOut := by
  rcases judged with
    ⟨kind, valid, bicyclic, sameFramework, sameBridgehead, sameParticipant,
      firstLong, secondLong,
      firstDirection, secondDirection, firstJudged, secondJudged, different, rfl⟩
  refine ⟨valid, ?_, kind, bicyclic, ?_⟩
  · simp [coordinateInOutRecord, P94ConformationEvidence.MolecularRolesValid]
  · exact ⟨sameFramework, sameBridgehead, sameParticipant,
      firstLong, secondLong, different⟩

/-- Successful paired evidence cannot combine opposite directions taken at different molecule
sites: framework identity, bridgehead atom ID, and directed participant ID all agree. -/
theorem coordinateInOutEvidenceJudgment_same_site {Framework : Type*}
    (premises : IndependentInOutPremises Framework) (molecule : RawMolecule)
    (input : CoordinateInOutInput Framework) (output : CoordinateInOutEvidence Framework)
    (judged : CoordinateInOutEvidenceJudgment premises molecule input output) :
    input.first.framework = input.second.framework ∧
      input.first.bridgehead = input.second.bridgehead ∧
      input.first.directedParticipant = input.second.directedParticipant := by
  rcases judged with
    ⟨_, _, _, sameFramework, sameBridgehead, sameParticipant, _⟩
  exact ⟨sameFramework, sameBridgehead, sameParticipant⟩

/-! ## Public analyzer closure: twist -/

noncomputable def coordinateTwistAssignments {State : Type*} [DecidableEq State]
    (certified : CertifiedChemistryNormalizationResult)
    (input : CoordinateTwistInput State) : List P94ConformationAssignment :=
  match coordinateTwistEvidence? certified.result.parsed input with
  | none => []
  | some output => certified.analyzeP94Conformation [output]

theorem coordinateTwistAssignments_mem_iff {State : Type*} [DecidableEq State]
    (certified : CertifiedChemistryNormalizationResult)
    (input : CoordinateTwistInput State) (assignment : P94ConformationAssignment) :
    assignment ∈ coordinateTwistAssignments certified input ↔
      ∃ output,
        CoordinateTwistEvidenceJudgment certified.result.parsed input output ∧
        IndependentP94ConformationAssignment certified.result.parsed [output] assignment := by
  classical
  cases computed : coordinateTwistEvidence? certified.result.parsed input with
  | none =>
      constructor
      · intro present
        unfold coordinateTwistAssignments at present
        rw [computed] at present
        simp at present
      · rintro ⟨output, judged, _⟩
        have some := (coordinateTwistEvidence?_eq_some_iff
          certified.result.parsed input output).mpr judged
        rw [computed] at some
        contradiction
  | some output =>
      constructor
      · intro present
        have analyzedPresent : assignment ∈ certified.analyzeP94Conformation [output] := by
          unfold coordinateTwistAssignments at present
          rw [computed] at present
          exact present
        have independent := (mem_analyzeP94Conformation_iff_independent
          certified [output] assignment).mp analyzedPresent
        exact ⟨output,
          (coordinateTwistEvidence?_eq_some_iff
            certified.result.parsed input output).mp computed,
          independent⟩
      · rintro ⟨other, judged, independent⟩
        have otherComputed := (coordinateTwistEvidence?_eq_some_iff
          certified.result.parsed input other).mpr judged
        rw [computed] at otherComputed
        have equal : output = other := Option.some.inj otherComputed
        subst other
        have analyzedPresent := (mem_analyzeP94Conformation_iff_independent
          certified [output] assignment).mpr independent
        unfold coordinateTwistAssignments
        rw [computed]
        exact analyzedPresent

theorem coordinateTwistAssignments_nodup {State : Type*} [DecidableEq State]
    (certified : CertifiedChemistryNormalizationResult)
    (input : CoordinateTwistInput State) :
    (coordinateTwistAssignments certified input).Nodup := by
  classical
  cases computed : coordinateTwistEvidence? certified.result.parsed input with
  | none =>
      unfold coordinateTwistAssignments
      rw [computed]
      simp
  | some output =>
      unfold coordinateTwistAssignments
      rw [computed]
      exact analyzeP94Conformation_nodup certified [output]

theorem coordinateTwistAssignment_count_eq_one_iff {State : Type*} [DecidableEq State]
    (certified : CertifiedChemistryNormalizationResult)
    (input : CoordinateTwistInput State) (assignment : P94ConformationAssignment) :
    List.count assignment (coordinateTwistAssignments certified input) = 1 ↔
      ∃ output,
        CoordinateTwistEvidenceJudgment certified.result.parsed input output ∧
        IndependentP94ConformationAssignment certified.result.parsed [output] assignment := by
  classical
  rw [← coordinateTwistAssignments_mem_iff]
  constructor
  · intro countOne
    by_contra absent
    have countZero : List.count assignment (coordinateTwistAssignments certified input) = 0 :=
      List.count_eq_zero_of_not_mem absent
    omega
  · exact List.count_eq_one_of_mem (coordinateTwistAssignments_nodup certified input)

theorem coordinateTwistEvidence_success_emits_twist_exactly_once {State : Type*}
    [DecidableEq State] (certified : CertifiedChemistryNormalizationResult)
    (input : CoordinateTwistInput State) (output : CoordinateTwistEvidence State)
    (computed : coordinateTwistEvidence? certified.result.parsed input = some output) :
    List.count
      ({ unit := output.unit, descriptor := .twist } : P94ConformationAssignment)
      (coordinateTwistAssignments certified input) = 1 := by
  have judged := (coordinateTwistEvidence?_eq_some_iff
    certified.result.parsed input output).mp computed
  rcases coordinateTwistEvidenceJudgment_supports_twist
    certified.result.parsed input output judged with ⟨valid, roles, support⟩
  apply (coordinateTwistAssignment_count_eq_one_iff certified input _).mpr
  exact ⟨output, judged, output, by simp, rfl, valid, roles, support⟩

/-! ## Public analyzer closure: in-out -/

noncomputable def coordinateInOutAssignments {Framework : Type*}
    (certified : CertifiedChemistryNormalizationResult)
    (premises : IndependentInOutPremises Framework)
    (input : CoordinateInOutInput Framework) : List P94ConformationAssignment :=
  match coordinateInOutEvidence? premises certified.result.parsed input with
  | none => []
  | some output => certified.analyzeP94Conformation [output]

theorem coordinateInOutAssignments_mem_iff {Framework : Type*}
    (certified : CertifiedChemistryNormalizationResult)
    (premises : IndependentInOutPremises Framework)
    (input : CoordinateInOutInput Framework) (assignment : P94ConformationAssignment) :
    assignment ∈ coordinateInOutAssignments certified premises input ↔
      ∃ output,
        CoordinateInOutEvidenceJudgment premises certified.result.parsed input output ∧
        IndependentP94ConformationAssignment certified.result.parsed [output] assignment := by
  classical
  cases computed : coordinateInOutEvidence? premises certified.result.parsed input with
  | none =>
      constructor
      · intro present
        unfold coordinateInOutAssignments at present
        rw [computed] at present
        simp at present
      · rintro ⟨output, judged, _⟩
        have some := (coordinateInOutEvidence?_eq_some_iff
          premises certified.result.parsed input output).mpr judged
        rw [computed] at some
        contradiction
  | some output =>
      constructor
      · intro present
        have analyzedPresent : assignment ∈ certified.analyzeP94Conformation [output] := by
          unfold coordinateInOutAssignments at present
          rw [computed] at present
          exact present
        have independent := (mem_analyzeP94Conformation_iff_independent
          certified [output] assignment).mp analyzedPresent
        exact ⟨output,
          (coordinateInOutEvidence?_eq_some_iff
            premises certified.result.parsed input output).mp computed,
          independent⟩
      · rintro ⟨other, judged, independent⟩
        have otherComputed := (coordinateInOutEvidence?_eq_some_iff
          premises certified.result.parsed input other).mpr judged
        rw [computed] at otherComputed
        have equal : output = other := Option.some.inj otherComputed
        subst other
        have analyzedPresent := (mem_analyzeP94Conformation_iff_independent
          certified [output] assignment).mpr independent
        unfold coordinateInOutAssignments
        rw [computed]
        exact analyzedPresent

theorem coordinateInOutAssignments_nodup {Framework : Type*}
    (certified : CertifiedChemistryNormalizationResult)
    (premises : IndependentInOutPremises Framework)
    (input : CoordinateInOutInput Framework) :
    (coordinateInOutAssignments certified premises input).Nodup := by
  classical
  cases computed : coordinateInOutEvidence? premises certified.result.parsed input with
  | none =>
      unfold coordinateInOutAssignments
      rw [computed]
      simp
  | some output =>
      unfold coordinateInOutAssignments
      rw [computed]
      exact analyzeP94Conformation_nodup certified [output]

theorem coordinateInOutAssignment_count_eq_one_iff {Framework : Type*}
    (certified : CertifiedChemistryNormalizationResult)
    (premises : IndependentInOutPremises Framework)
    (input : CoordinateInOutInput Framework) (assignment : P94ConformationAssignment) :
    List.count assignment (coordinateInOutAssignments certified premises input) = 1 ↔
      ∃ output,
        CoordinateInOutEvidenceJudgment premises certified.result.parsed input output ∧
        IndependentP94ConformationAssignment certified.result.parsed [output] assignment := by
  classical
  rw [← coordinateInOutAssignments_mem_iff]
  constructor
  · intro countOne
    by_contra absent
    have countZero : List.count assignment
        (coordinateInOutAssignments certified premises input) = 0 :=
      List.count_eq_zero_of_not_mem absent
    omega
  · exact List.count_eq_one_of_mem
      (coordinateInOutAssignments_nodup certified premises input)

theorem coordinateInOutEvidence_success_emits_inOut_exactly_once {Framework : Type*}
    (certified : CertifiedChemistryNormalizationResult)
    (premises : IndependentInOutPremises Framework)
    (input : CoordinateInOutInput Framework) (output : CoordinateInOutEvidence Framework)
    (computed : coordinateInOutEvidence? premises certified.result.parsed input = some output) :
    List.count
      ({ unit := output.unit, descriptor := .inOut } : P94ConformationAssignment)
      (coordinateInOutAssignments certified premises input) = 1 := by
  have judged := (coordinateInOutEvidence?_eq_some_iff
    premises certified.result.parsed input output).mp computed
  rcases coordinateInOutEvidenceJudgment_supports_inOut
    premises certified.result.parsed input output judged with ⟨valid, roles, support⟩
  apply (coordinateInOutAssignment_count_eq_one_iff certified premises input _).mpr
  exact ⟨output, judged, output, by simp, rfl, valid, roles, support⟩

end BlueBookP94.CoordinateTwistInOut
end TetraStereo.OneCenter
