import TetraStereo.OneCenter.AuthoritativeSemanticOpenCumuleneCarrierPerception
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeConcreteUnifiedAnalysis

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Source-canonical planar odd-open-cumulene analysis

This is the descriptor-producing insertion for the exhaustive odd-open-cumulene carriers.  Both
terminal ligand frames use the same concrete Rules-3--5 fixed point as the tetrahedral and ordinary
double-bond branches.  Exact rational terminal geometry and independently derived Rule-5 parity
then select the final ordinary or sequence double-bond descriptor family.
-/

/-- The two terminal atoms and their inward cumulene partners. -/
structure AromaticCanonicalOpenCumuleneTerminals
    (source : AuthoritativeChemicalInput) where
  left : source.AromaticCanonicalAtom
  leftPartner : source.AromaticCanonicalAtom
  rightPartner : source.AromaticCanonicalAtom
  right : source.AromaticCanonicalAtom
  deriving DecidableEq

def aromaticCanonicalCumuleneLeft?
    {source : AuthoritativeChemicalInput}
    (path : List source.AromaticCanonicalAtom) := path.head?

def aromaticCanonicalCumuleneLeftPartner?
    {source : AuthoritativeChemicalInput}
    (path : List source.AromaticCanonicalAtom) := path.tail.head?

def aromaticCanonicalCumuleneRight?
    {source : AuthoritativeChemicalInput}
    (path : List source.AromaticCanonicalAtom) := path.reverse.head?

def aromaticCanonicalCumuleneRightPartner?
    {source : AuthoritativeChemicalInput}
    (path : List source.AromaticCanonicalAtom) := path.reverse.tail.head?

/-- Read both oriented terminal pairs from a canonical physical path. -/
def aromaticCanonicalOpenCumuleneTerminals?
    (source : AuthoritativeChemicalInput)
    (path : List source.AromaticCanonicalAtom) :
    Option source.AromaticCanonicalOpenCumuleneTerminals := do
  let left ← aromaticCanonicalCumuleneLeft? path
  let leftPartner ← aromaticCanonicalCumuleneLeftPartner? path
  let right ← aromaticCanonicalCumuleneRight? path
  let rightPartner ← aromaticCanonicalCumuleneRightPartner? path
  some { left, leftPartner, rightPartner, right }

/-- Independent exact meaning of terminal extraction. -/
def DeclarativeAromaticCanonicalOpenCumuleneTerminals
    (source : AuthoritativeChemicalInput)
    (path : List source.AromaticCanonicalAtom)
    (terminals : source.AromaticCanonicalOpenCumuleneTerminals) : Prop :=
  aromaticCanonicalCumuleneLeft? path = some terminals.left ∧
    aromaticCanonicalCumuleneLeftPartner? path = some terminals.leftPartner ∧
    aromaticCanonicalCumuleneRight? path = some terminals.right ∧
    aromaticCanonicalCumuleneRightPartner? path = some terminals.rightPartner

/-- Terminal extraction is exact, including its short-path refusal boundary. -/
theorem aromaticCanonicalOpenCumuleneTerminals?_eq_some_iff
    (source : AuthoritativeChemicalInput)
    (path : List source.AromaticCanonicalAtom)
    (terminals : source.AromaticCanonicalOpenCumuleneTerminals) :
    source.aromaticCanonicalOpenCumuleneTerminals? path = some terminals ↔
      source.DeclarativeAromaticCanonicalOpenCumuleneTerminals path terminals := by
  cases terminals with
  | mk left leftPartner rightPartner right =>
      unfold aromaticCanonicalOpenCumuleneTerminals?
        DeclarativeAromaticCanonicalOpenCumuleneTerminals
      constructor
      · intro computed
        cases leftComputed : aromaticCanonicalCumuleneLeft? path with
        | none => simp [leftComputed] at computed
        | some observedLeft =>
          cases leftPartnerComputed : aromaticCanonicalCumuleneLeftPartner? path with
          | none => simp [leftComputed, leftPartnerComputed] at computed
          | some observedLeftPartner =>
            cases rightComputed : aromaticCanonicalCumuleneRight? path with
            | none =>
                simp [leftComputed, leftPartnerComputed, rightComputed] at computed
            | some observedRight =>
              cases rightPartnerComputed : aromaticCanonicalCumuleneRightPartner? path with
              | none =>
                  simp [leftComputed, leftPartnerComputed, rightComputed,
                    rightPartnerComputed] at computed
              | some observedRightPartner =>
                  simp [leftComputed, leftPartnerComputed, rightComputed,
                    rightPartnerComputed] at computed
                  rcases computed with ⟨rfl, rfl, rfl, rfl⟩
                  exact ⟨rfl, rfl, rfl, rfl⟩
      · rintro ⟨leftComputed, leftPartnerComputed,
          rightComputed, rightPartnerComputed⟩
        simp [leftComputed, leftPartnerComputed, rightComputed,
          rightPartnerComputed]

/-- One final source-indexed planar odd-cumulene assignment. -/
structure AromaticCanonicalOddOpenCumuleneSpatialAssignment
    (source : AuthoritativeChemicalInput) where
  unit : List source.AromaticCanonicalAtom
  terminals : source.AromaticCanonicalOpenCumuleneTerminals
  leftReference : source.AromaticCanonicalAtom
  rightReference : source.AromaticCanonicalAtom
  geometry : OfficialRule3Geometry
  outcome : StereoOutcome
  deriving DecidableEq

/-- Analyze one canonical odd-open-cumulene physical unit. -/
noncomputable def aromaticCanonicalOddOpenCumuleneSpatialAssignment?
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom) :
    Option source.AromaticCanonicalOddOpenCumuleneSpatialAssignment := do
  let terminals ← source.aromaticCanonicalOpenCumuleneTerminals? unit
  let leftView := source.aromaticCanonicalConcreteDependencyViewAt
    carrierFuel ruleFuel terminals.left
  let rightView := source.aromaticCanonicalConcreteDependencyViewAt
    carrierFuel ruleFuel terminals.right
  let leftFrame ←
    source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
      carrierFuel terminals.left terminals.leftPartner leftView
        (2 * (carrierFuel + 1))
  let rightFrame ←
    source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
      carrierFuel terminals.right terminals.rightPartner rightView
        (2 * (carrierFuel + 1))
  let leftSelection ←
    source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection? leftFrame
  let rightSelection ←
    source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection? rightFrame
  let leftPoint ← source.aromaticCanonicalSpatialPointAt? terminals.left
  let rightPoint ← source.aromaticCanonicalSpatialPointAt? terminals.right
  let leftReferencePoint ←
    source.aromaticCanonicalSpatialPointAt? leftSelection.reference
  let rightReferencePoint ←
    source.aromaticCanonicalSpatialPointAt? rightSelection.reference
  let geometry ← rule3GeometryOfSpatialReferences? leftPoint rightPoint
    leftReferencePoint rightReferencePoint
  let outcome ← aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
    leftSelection.enantiomorphic rightSelection.enantiomorphic geometry
  some {
    unit
    terminals
    leftReference := leftSelection.reference
    rightReference := rightSelection.reference
    geometry
    outcome
  }

/-- Independent meaning of a final odd-open-cumulene assignment. -/
def DeclarativeAromaticCanonicalOddOpenCumuleneSpatialAssignment
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalOddOpenCumuleneSpatialAssignment) : Prop :=
  assignment.unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits ∧
    source.DeclarativeAromaticCanonicalOpenCumuleneTerminals
      assignment.unit assignment.terminals ∧
    ∃ leftFrame rightFrame leftSelection rightSelection
        leftPoint rightPoint leftReferencePoint rightReferencePoint,
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
        carrierFuel assignment.terminals.left assignment.terminals.leftPartner
        (source.aromaticCanonicalConcreteDependencyViewAt
          carrierFuel ruleFuel assignment.terminals.left)
        (2 * (carrierFuel + 1)) leftFrame ∧
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
        carrierFuel assignment.terminals.right assignment.terminals.rightPartner
        (source.aromaticCanonicalConcreteDependencyViewAt
          carrierFuel ruleFuel assignment.terminals.right)
        (2 * (carrierFuel + 1)) rightFrame ∧
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
        leftFrame leftSelection ∧
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
        rightFrame rightSelection ∧
      assignment.leftReference = leftSelection.reference ∧
      assignment.rightReference = rightSelection.reference ∧
      source.SemanticAromaticCanonicalSpatialPointAt
        assignment.terminals.left leftPoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt
        assignment.terminals.right rightPoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt
        leftSelection.reference leftReferencePoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt
        rightSelection.reference rightReferencePoint ∧
      RationalRule3SpatialGeometry leftPoint rightPoint
        leftReferencePoint rightReferencePoint assignment.geometry ∧
      AromaticCanonicalOrdinaryDoubleBondPlanarOutcomeJudgment
        leftSelection.enantiomorphic rightSelection.enantiomorphic
        assignment.geometry assignment.outcome

set_option maxHeartbeats 1000000 in
/-- Every emitted odd-open-cumulene descriptor has independent exhaustive topology, terminal
Rules-1a--5 priorities, Rule-5 parity, exact source coordinates, rational geometry, and final
descriptor-family meaning. -/
theorem aromaticCanonicalOddOpenCumuleneSpatialAssignment?_sound
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits)
    (assignment : source.AromaticCanonicalOddOpenCumuleneSpatialAssignment)
    (computed : source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?
      carrierFuel ruleFuel unit = some assignment) :
    source.DeclarativeAromaticCanonicalOddOpenCumuleneSpatialAssignment
      carrierFuel ruleFuel assignment := by
  unfold aromaticCanonicalOddOpenCumuleneSpatialAssignment? at computed
  cases terminalsComputed : source.aromaticCanonicalOpenCumuleneTerminals? unit with
  | none => simp [terminalsComputed] at computed
  | some terminals =>
    cases leftFrameComputed :
        source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
          carrierFuel terminals.left terminals.leftPartner
          (source.aromaticCanonicalConcreteDependencyViewAt
            carrierFuel ruleFuel terminals.left)
          (2 * (carrierFuel + 1)) with
    | none => simp [terminalsComputed, leftFrameComputed] at computed
    | some leftFrame =>
      cases rightFrameComputed :
          source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
            carrierFuel terminals.right terminals.rightPartner
            (source.aromaticCanonicalConcreteDependencyViewAt
              carrierFuel ruleFuel terminals.right)
            (2 * (carrierFuel + 1)) with
      | none =>
          simp [terminalsComputed, leftFrameComputed, rightFrameComputed] at computed
      | some rightFrame =>
        cases leftSelectionComputed :
            source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?
              leftFrame with
        | none =>
            simp [terminalsComputed, leftFrameComputed, rightFrameComputed,
              leftSelectionComputed] at computed
        | some leftSelection =>
          cases rightSelectionComputed :
              source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?
                rightFrame with
          | none =>
              simp [terminalsComputed, leftFrameComputed, rightFrameComputed,
                rightSelectionComputed] at computed
          | some rightSelection =>
            cases leftPointComputed :
                source.aromaticCanonicalSpatialPointAt? terminals.left with
            | none =>
                simp [terminalsComputed, leftFrameComputed, rightFrameComputed,
                  leftPointComputed] at computed
            | some leftPoint =>
              cases rightPointComputed :
                  source.aromaticCanonicalSpatialPointAt? terminals.right with
              | none =>
                  simp [terminalsComputed, leftFrameComputed, rightFrameComputed,
                    leftPointComputed, rightPointComputed] at computed
              | some rightPoint =>
                cases leftReferencePointComputed :
                    source.aromaticCanonicalSpatialPointAt?
                      leftSelection.reference with
                | none =>
                    simp [terminalsComputed, leftFrameComputed, rightFrameComputed,
                      leftSelectionComputed, rightSelectionComputed,
                      leftPointComputed, rightPointComputed,
                      leftReferencePointComputed] at computed
                | some leftReferencePoint =>
                  cases rightReferencePointComputed :
                      source.aromaticCanonicalSpatialPointAt?
                        rightSelection.reference with
                  | none =>
                      simp [terminalsComputed, leftFrameComputed, rightFrameComputed,
                        rightSelectionComputed,
                        leftPointComputed, rightPointComputed,
                        rightReferencePointComputed] at computed
                  | some rightReferencePoint =>
                    cases geometryComputed : rule3GeometryOfSpatialReferences?
                        leftPoint rightPoint leftReferencePoint
                          rightReferencePoint with
                    | none =>
                        simp [terminalsComputed, leftFrameComputed,
                          rightFrameComputed, leftSelectionComputed,
                          rightSelectionComputed, leftPointComputed,
                          rightPointComputed, leftReferencePointComputed,
                          rightReferencePointComputed, geometryComputed] at computed
                    | some geometry =>
                      cases outcomeComputed :
                          aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
                            leftSelection.enantiomorphic
                            rightSelection.enantiomorphic geometry with
                      | none =>
                          simp [terminalsComputed, leftFrameComputed,
                            rightFrameComputed, leftSelectionComputed,
                            rightSelectionComputed, leftPointComputed,
                            rightPointComputed, leftReferencePointComputed,
                            rightReferencePointComputed, geometryComputed,
                            outcomeComputed] at computed
                      | some outcome =>
                        simp [terminalsComputed, leftFrameComputed,
                          rightFrameComputed, leftSelectionComputed,
                          rightSelectionComputed, leftPointComputed,
                          rightPointComputed, leftReferencePointComputed,
                          rightReferencePointComputed, geometryComputed,
                          outcomeComputed] at computed
                        subst assignment
                        exact ⟨owner,
                          (source.aromaticCanonicalOpenCumuleneTerminals?_eq_some_iff
                            unit terminals).mp terminalsComputed,
                          leftFrame, rightFrame, leftSelection, rightSelection,
                          leftPoint, rightPoint, leftReferencePoint,
                          rightReferencePoint,
                          source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?_sound
                            carrierFuel terminals.left terminals.leftPartner
                            (source.aromaticCanonicalConcreteDependencyViewAt
                              carrierFuel ruleFuel terminals.left)
                            (2 * (carrierFuel + 1)) leftFrame leftFrameComputed,
                          source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?_sound
                            carrierFuel terminals.right terminals.rightPartner
                            (source.aromaticCanonicalConcreteDependencyViewAt
                              carrierFuel ruleFuel terminals.right)
                            (2 * (carrierFuel + 1)) rightFrame rightFrameComputed,
                          source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_sound
                            leftFrame leftSelection leftSelectionComputed,
                          source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_sound
                            rightFrame rightSelection rightSelectionComputed,
                          rfl, rfl,
                          (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
                            terminals.left leftPoint).mp leftPointComputed,
                          (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
                            terminals.right rightPoint).mp rightPointComputed,
                          (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
                            leftSelection.reference leftReferencePoint).mp
                              leftReferencePointComputed,
                          (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
                            rightSelection.reference rightReferencePoint).mp
                              rightReferencePointComputed,
                          (rule3GeometryOfSpatialReferences?_eq_some_iff
                            leftPoint rightPoint leftReferencePoint
                              rightReferencePoint geometry).mp geometryComputed,
                          (aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?_eq_some_iff
                            leftSelection.enantiomorphic
                            rightSelection.enantiomorphic geometry outcome).mp
                              outcomeComputed⟩

/-- Whole-molecule analysis of every canonical odd-open-cumulene physical unit. -/
noncomputable def analyzeAromaticCanonicalOddOpenCumuleneSpatial
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat) :
    List source.AromaticCanonicalOddOpenCumuleneSpatialAssignment :=
  source.aromaticCanonicalOddOpenCumuleneUnits.filterMap fun unit =>
    source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?
      carrierFuel ruleFuel unit

/-- Exact executable membership of the whole odd-open-cumulene analyzer. -/
theorem mem_analyzeAromaticCanonicalOddOpenCumuleneSpatial_iff
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalOddOpenCumuleneSpatialAssignment) :
    assignment ∈ source.analyzeAromaticCanonicalOddOpenCumuleneSpatial
        carrierFuel ruleFuel ↔
      ∃ unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits,
        source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?
          carrierFuel ruleFuel unit = some assignment := by
  rw [analyzeAromaticCanonicalOddOpenCumuleneSpatial, List.mem_filterMap]

/-- Every whole-molecule odd-open-cumulene result satisfies the independent source topology,
priority, parity, geometry, and descriptor judgment. -/
theorem analyzeAromaticCanonicalOddOpenCumuleneSpatial_member_sound
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalOddOpenCumuleneSpatialAssignment)
    (present : assignment ∈ source.analyzeAromaticCanonicalOddOpenCumuleneSpatial
      carrierFuel ruleFuel) :
    source.DeclarativeAromaticCanonicalOddOpenCumuleneSpatialAssignment
      carrierFuel ruleFuel assignment := by
  obtain ⟨unit, owner, emitted⟩ :=
    (source.mem_analyzeAromaticCanonicalOddOpenCumuleneSpatial_iff
      carrierFuel ruleFuel assignment).mp present
  exact source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?_sound
    carrierFuel ruleFuel unit owner assignment emitted

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
