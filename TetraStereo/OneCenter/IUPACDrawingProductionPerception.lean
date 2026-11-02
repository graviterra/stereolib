import TetraStereo.OneCenter.AuthoritativeChemicalInput
import TetraStereo.OneCenter.GraphicalRepresentationST3to6

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Executable perception of the production drawing vocabulary

`AuthoritativeChemicalInput` deliberately stores a small, format-neutral diagram vocabulary,
whereas the independent 2006 IUPAC drawing reference uses the more detailed ST-0--ST-6 types.
This module gives every production constructor one total meaning.  The two SMILES directional
markers are kept distinct from stereobonds: treating `/` or `\` as a wedge would be a semantic
error.

This is the common ingress for later unit-specific drawing recognizers.  It certifies what the
production record literally says; it does not infer unrecorded perspective or chemical facts.
-/

namespace IUPACDrawing2006.ProductionPerception

open ST0

namespace DiagramBondStyle

/-- Exact embedding of production graphical styles into ST-0.  Directional alkene markers are
not ST-0 bond-depth styles and are therefore deliberately outside this partial embedding. -/
def toST0BondStyle? : DiagramBondStyle → Option ST0.BondStyle
  | .plain => some .plain
  | .solidWedge => some .solidWedge
  | .hashedWedge => some .hashedWedge
  | .wavy => some .wavy
  | .bold => some .unwedgedBold
  | .directionalUp | .directionalDown => none

end DiagramBondStyle

/-- The parser's two directed single-bond markers used to encode adjacent double-bond geometry. -/
inductive AlkeneDirectionalMarker where
  | up
  | down
  deriving DecidableEq, Repr

/-- Total semantic classification of a production diagram bond. -/
inductive BondMeaning where
  | st0 (bond : ST0.OrientedBond) (interpretation : ST0.Interpretation)
  | alkeneDirectional (marker : AlkeneDirectionalMarker)
  deriving DecidableEq, Repr

/-- A perceived bond retains its molecular endpoints and configuration scope verbatim. -/
structure PerceivedBond where
  source : Nat
  target : Nat
  scope : DiagramConfigurationScope
  meaning : BondMeaning
  deriving DecidableEq, Repr

/-- Interpret every production style.  Production wedges are directed from their narrow
`source` endpoint to their wide `target` endpoint. -/
def interpretBond (bond : DiagramBond) : PerceivedBond :=
  let meaning :=
    match bond.style with
    | .directionalUp => BondMeaning.alkeneDirectional .up
    | .directionalDown => BondMeaning.alkeneDirectional .down
    | .plain =>
        let oriented : ST0.OrientedBond := { style := .plain, narrowEnd := .source }
        BondMeaning.st0 oriented (ST0.preferredInterpretation oriented)
    | .solidWedge =>
        let oriented : ST0.OrientedBond := { style := .solidWedge, narrowEnd := .source }
        BondMeaning.st0 oriented (ST0.preferredInterpretation oriented)
    | .hashedWedge =>
        let oriented : ST0.OrientedBond := { style := .hashedWedge, narrowEnd := .source }
        BondMeaning.st0 oriented (ST0.preferredInterpretation oriented)
    | .wavy =>
        let oriented : ST0.OrientedBond := { style := .wavy, narrowEnd := .source }
        BondMeaning.st0 oriented (ST0.preferredInterpretation oriented)
    | .bold =>
        let oriented : ST0.OrientedBond := { style := .unwedgedBold, narrowEnd := .source }
        BondMeaning.st0 oriented (ST0.preferredInterpretation oriented)
  { source := bond.source, target := bond.target, scope := bond.scope, meaning := meaning }

namespace DiagramConfigurationScope

/-- ST-6 knowledge state literally asserted by the production scope.  A bare `.unknown` scope
still denotes one drawn stereoisomer whose absolute configuration is unknown; it is not a claim
that the molecular entity has no stereochemical information. -/
def configurationKnowledge : DiagramConfigurationScope → ST6.ConfigurationKnowledge
  | .absolute => .knownAbsolute
  | .relative _ => .knownRelative
  | .racemic _ => .racemic
  | .unknown => .unknownAbsoluteSingleStereoisomer

end DiagramConfigurationScope

/-- Perception of an explicit atom-parity statement. -/
structure PerceivedAtomConfiguration where
  atom : Nat
  parity : TetrahedralInputParity
  scope : DiagramConfigurationScope
  knowledge : ST6.ConfigurationKnowledge
  deriving DecidableEq, Repr

def interpretAtomConfiguration
    (configuration : DiagramAtomConfiguration) : PerceivedAtomConfiguration :=
  { atom := configuration.atom
    parity := configuration.parity
    scope := configuration.scope
    knowledge := DiagramConfigurationScope.configurationKnowledge configuration.scope }

/-- Fully interpreted production diagram.  Coordinates are retained because subsequent ST-2,
ST-3, and ST-5 recognizers need the exact drawing geometry. -/
structure PerceivedDiagram where
  atomPositions? : Option (List CartesianPoint2)
  bonds : List PerceivedBond
  atomConfigurations : List PerceivedAtomConfiguration
  deriving DecidableEq, Repr

def interpretDiagram (diagram : DiagramConfiguration) : PerceivedDiagram :=
  { atomPositions? := diagram.atomPositions?
    bonds := diagram.bonds.map interpretBond
    atomConfigurations := diagram.atomConfigurations.map interpretAtomConfiguration }

/-- Independent finite-index admissibility condition for a standalone diagram. -/
def DiagramWellFormed (atomCount : Nat) (diagram : DiagramConfiguration) : Prop :=
  (match diagram.atomPositions? with
   | none => True
   | some positions => positions.length = atomCount) ∧
  (∀ bond ∈ diagram.bonds,
    bond.source < atomCount ∧ bond.target < atomCount ∧ bond.source ≠ bond.target) ∧
  (∀ configuration ∈ diagram.atomConfigurations, configuration.atom < atomCount)

def diagramWellFormed? (atomCount : Nat) (diagram : DiagramConfiguration) : Bool :=
  (match diagram.atomPositions? with
   | none => true
   | some positions => decide (positions.length = atomCount)) &&
  diagram.bonds.all (fun bond =>
    decide (bond.source < atomCount) && decide (bond.target < atomCount) &&
      decide (bond.source ≠ bond.target)) &&
  diagram.atomConfigurations.all (fun configuration =>
    decide (configuration.atom < atomCount))

@[simp] theorem diagramWellFormed?_eq_true_iff
    (atomCount : Nat) (diagram : DiagramConfiguration) :
    diagramWellFormed? atomCount diagram = true ↔ DiagramWellFormed atomCount diagram := by
  cases positionsObserved : diagram.atomPositions? <;>
    simp [diagramWellFormed?, DiagramWellFormed, positionsObserved, and_assoc]

/-- Independent meaning of successful whole-diagram perception. -/
def DiagramPerceptionJudgment
    (atomCount : Nat) (diagram : DiagramConfiguration) (perceived : PerceivedDiagram) : Prop :=
  DiagramWellFormed atomCount diagram ∧ perceived = interpretDiagram diagram

/-- Refuse malformed indices; otherwise interpret every diagram constructor. -/
def perceiveDiagram? (atomCount : Nat) (diagram : DiagramConfiguration) :
    Option PerceivedDiagram :=
  if diagramWellFormed? atomCount diagram then some (interpretDiagram diagram) else none

theorem perceiveDiagram?_eq_some_iff
    (atomCount : Nat) (diagram : DiagramConfiguration) (perceived : PerceivedDiagram) :
    perceiveDiagram? atomCount diagram = some perceived ↔
      DiagramPerceptionJudgment atomCount diagram perceived := by
  unfold DiagramPerceptionJudgment
  by_cases checked : diagramWellFormed? atomCount diagram = true
  · have wellFormed : DiagramWellFormed atomCount diagram :=
      (diagramWellFormed?_eq_true_iff atomCount diagram).mp checked
    constructor
    · intro computed
      have equality : interpretDiagram diagram = perceived := by
        exact Option.some.inj (by simpa [perceiveDiagram?, checked] using computed)
      exact ⟨wellFormed, equality.symm⟩
    · rintro ⟨_, rfl⟩
      simp [perceiveDiagram?, checked]
  · have notWellFormed : ¬DiagramWellFormed atomCount diagram := by
      intro wellFormed
      exact checked ((diagramWellFormed?_eq_true_iff atomCount diagram).mpr wellFormed)
    simp [perceiveDiagram?, checked, notWellFormed]

theorem perceiveDiagram?_eq_none_iff
    (atomCount : Nat) (diagram : DiagramConfiguration) :
    perceiveDiagram? atomCount diagram = none ↔ ¬DiagramWellFormed atomCount diagram := by
  rw [← diagramWellFormed?_eq_true_iff]
  simp [perceiveDiagram?]

end IUPACDrawing2006.ProductionPerception

end TetraStereo.OneCenter
