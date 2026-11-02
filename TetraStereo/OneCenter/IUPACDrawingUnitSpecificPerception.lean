import TetraStereo.OneCenter.IUPACDrawingProductionPerception

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace IUPACDrawing2006.UnitSpecificPerception

open ST0
open ProductionPerception

/-!
# Unit-specific evidence from production drawings

The production ingress classifies every graphical object. This layer extracts only statements
that can participate in stereochemical-unit perception: in-plane depth from a plain bond,
directed wedge depth at the narrow atom, unknown configuration from a wavy bond,
alkene-direction markers, and explicit atom parity. An unwedged-bold bond remains a
perspective object and does not become local configuration evidence.
-/

inductive DrawingUnitEvidence where
  | localDepth (center other : Nat) (depth : ST0.Depth)
      (scope : DiagramConfigurationScope)
  | unknownBondConfiguration (first second : Nat)
      (scope : DiagramConfigurationScope)
  | alkeneDirectional (source target : Nat) (marker : AlkeneDirectionalMarker)
  | explicitAtomParity (atom : Nat) (parity : TetrahedralInputParity)
      (scope : DiagramConfigurationScope) (knowledge : ST6.ConfigurationKnowledge)
  deriving DecidableEq, Repr

/-- Independent constructor-by-constructor meaning of a unit-specific bond cue. -/
def BondUnitEvidenceJudgment (bond : DiagramBond) (evidence : DrawingUnitEvidence) : Prop :=
  match bond.style with
  | .plain =>
      evidence = .localDepth bond.source bond.target .inPlane bond.scope
  | .solidWedge =>
      evidence = .localDepth bond.source bond.target .abovePlane bond.scope
  | .hashedWedge =>
      evidence = .localDepth bond.source bond.target .belowPlane bond.scope
  | .wavy =>
      evidence = .unknownBondConfiguration bond.source bond.target bond.scope
  | .directionalUp =>
      evidence = .alkeneDirectional bond.source bond.target .up
  | .directionalDown =>
      evidence = .alkeneDirectional bond.source bond.target .down
  | .bold => False

/-- Extract the one unit-specific cue made by a bond, if any. -/
def perceiveBondUnitEvidence? (bond : DiagramBond) : Option DrawingUnitEvidence :=
  match bond.style with
  | .plain =>
      some (.localDepth bond.source bond.target .inPlane bond.scope)
  | .solidWedge =>
      some (.localDepth bond.source bond.target .abovePlane bond.scope)
  | .hashedWedge =>
      some (.localDepth bond.source bond.target .belowPlane bond.scope)
  | .wavy =>
      some (.unknownBondConfiguration bond.source bond.target bond.scope)
  | .directionalUp => some (.alkeneDirectional bond.source bond.target .up)
  | .directionalDown => some (.alkeneDirectional bond.source bond.target .down)
  | .bold => none

theorem perceiveBondUnitEvidence?_eq_some_iff
    (bond : DiagramBond) (evidence : DrawingUnitEvidence) :
    perceiveBondUnitEvidence? bond = some evidence ↔
      BondUnitEvidenceJudgment bond evidence := by
  cases bond with
  | mk source target style scope =>
      cases style <;> cases evidence <;>
        simp [perceiveBondUnitEvidence?, BondUnitEvidenceJudgment, eq_comm]

theorem perceiveBondUnitEvidence?_eq_none_iff
    (bond : DiagramBond) :
    perceiveBondUnitEvidence? bond = none ↔
      ∀ evidence, ¬ BondUnitEvidenceJudgment bond evidence := by
  constructor
  · intro computed evidence judged
    have someComputed :=
      (perceiveBondUnitEvidence?_eq_some_iff bond evidence).mpr judged
    rw [computed] at someComputed
    contradiction
  · intro absent
    cases computed : perceiveBondUnitEvidence? bond with
    | none => rfl
    | some evidence =>
        exact False.elim (absent evidence
          ((perceiveBondUnitEvidence?_eq_some_iff bond evidence).mp computed))

/-- Independent meaning of an explicit atom-parity cue and its ST-6 scope state. -/
def AtomUnitEvidenceJudgment
    (configuration : DiagramAtomConfiguration) (evidence : DrawingUnitEvidence) : Prop :=
  evidence = .explicitAtomParity configuration.atom configuration.parity configuration.scope
    (DiagramConfigurationScope.configurationKnowledge configuration.scope)

def perceiveAtomUnitEvidence
    (configuration : DiagramAtomConfiguration) : DrawingUnitEvidence :=
  .explicitAtomParity configuration.atom configuration.parity configuration.scope
    (DiagramConfigurationScope.configurationKnowledge configuration.scope)

theorem perceiveAtomUnitEvidence_iff
    (configuration : DiagramAtomConfiguration) (evidence : DrawingUnitEvidence) :
    perceiveAtomUnitEvidence configuration = evidence ↔
      AtomUnitEvidenceJudgment configuration evidence := by
  cases configuration with
  | mk atom parity scope =>
      cases evidence <;> simp [perceiveAtomUnitEvidence, AtomUnitEvidenceJudgment, eq_comm]

/-- Independent recursive semantics of filtering a source list through a partial relation. -/
inductive FilterMapJudgment {Alpha Beta : Type*} (relation : Alpha → Beta → Prop) :
    List Alpha → List Beta → Prop where
  | nil : FilterMapJudgment relation [] []
  | skip {source sources outputs}
      (absent : ∀ output, ¬ relation source output)
      (tail : FilterMapJudgment relation sources outputs) :
      FilterMapJudgment relation (source :: sources) outputs
  | emit {source sources output outputs}
      (head : relation source output)
      (tail : FilterMapJudgment relation sources outputs) :
      FilterMapJudgment relation (source :: sources) (output :: outputs)

theorem filterMap_perceiveBondUnitEvidence?_iff
    (bonds : List DiagramBond) (outputs : List DrawingUnitEvidence) :
    bonds.filterMap perceiveBondUnitEvidence? = outputs ↔
      FilterMapJudgment BondUnitEvidenceJudgment bonds outputs := by
  constructor
  · intro computed
    induction bonds generalizing outputs with
    | nil =>
        simp at computed
        subst outputs
        exact .nil
    | cons bond bonds inductionHypothesis =>
        cases localComputed : perceiveBondUnitEvidence? bond with
        | none =>
            simp [localComputed] at computed
            exact .skip
              ((perceiveBondUnitEvidence?_eq_none_iff bond).mp localComputed)
              (inductionHypothesis _ computed)
        | some evidence =>
            simp [localComputed] at computed
            subst outputs
            exact .emit
              ((perceiveBondUnitEvidence?_eq_some_iff bond evidence).mp localComputed)
              (inductionHypothesis _ rfl)
  · intro judged
    induction judged with
    | nil => rfl
    | skip absent tail inductionHypothesis =>
        have localComputed := (perceiveBondUnitEvidence?_eq_none_iff _).mpr absent
        simp [localComputed, inductionHypothesis]
    | emit head tail inductionHypothesis =>
        have localComputed := (perceiveBondUnitEvidence?_eq_some_iff _ _).mpr head
        simp [localComputed, inductionHypothesis]

theorem map_perceiveAtomUnitEvidence_iff
    (configurations : List DiagramAtomConfiguration)
    (outputs : List DrawingUnitEvidence) :
    configurations.map perceiveAtomUnitEvidence = outputs ↔
      List.Forall₂ AtomUnitEvidenceJudgment configurations outputs := by
  constructor
  · intro computed
    induction configurations generalizing outputs with
    | nil =>
        simp at computed
        subst outputs
        exact .nil
    | cons configuration configurations inductionHypothesis =>
        simp at computed
        subst outputs
        exact .cons
          ((perceiveAtomUnitEvidence_iff configuration _).mp rfl)
          (inductionHypothesis _ rfl)
  · intro judged
    induction judged with
    | nil => rfl
    | cons head tail inductionHypothesis =>
        have localComputed := (perceiveAtomUnitEvidence_iff _ _).mpr head
        simp [localComputed, inductionHypothesis]

/-- Independent whole-diagram meaning, preserving bond-cue order before atom-parity order. -/
def UnitSpecificDrawingPerceptionJudgment
    (atomCount : Nat) (diagram : DiagramConfiguration)
    (evidence : List DrawingUnitEvidence) : Prop :=
  ProductionPerception.DiagramWellFormed atomCount diagram ∧
    ∃ bondEvidence atomEvidence,
      FilterMapJudgment BondUnitEvidenceJudgment diagram.bonds bondEvidence ∧
      List.Forall₂ AtomUnitEvidenceJudgment diagram.atomConfigurations atomEvidence ∧
      evidence = bondEvidence ++ atomEvidence

/-- Refuse malformed diagrams; otherwise extract every represented unit-specific cue. -/
def perceiveUnitSpecificDrawing? (atomCount : Nat) (diagram : DiagramConfiguration) :
    Option (List DrawingUnitEvidence) := do
  let _ ← ProductionPerception.perceiveDiagram? atomCount diagram
  some
    (diagram.bonds.filterMap perceiveBondUnitEvidence? ++
      diagram.atomConfigurations.map perceiveAtomUnitEvidence)

theorem perceiveUnitSpecificDrawing?_eq_some_iff
    (atomCount : Nat) (diagram : DiagramConfiguration)
    (evidence : List DrawingUnitEvidence) :
    perceiveUnitSpecificDrawing? atomCount diagram = some evidence ↔
      UnitSpecificDrawingPerceptionJudgment atomCount diagram evidence := by
  constructor
  · intro computed
    unfold perceiveUnitSpecificDrawing? at computed
    cases perceivedComputed : ProductionPerception.perceiveDiagram? atomCount diagram with
    | none => simp [perceivedComputed] at computed
    | some perceived =>
        have wellFormed :=
          (ProductionPerception.perceiveDiagram?_eq_some_iff
            atomCount diagram perceived).mp perceivedComputed |>.1
        have evidenceEqual : evidence =
            diagram.bonds.filterMap perceiveBondUnitEvidence? ++
              diagram.atomConfigurations.map perceiveAtomUnitEvidence := by
          simpa [perceivedComputed] using computed.symm
        exact ⟨wellFormed,
          diagram.bonds.filterMap perceiveBondUnitEvidence?,
          diagram.atomConfigurations.map perceiveAtomUnitEvidence,
          (filterMap_perceiveBondUnitEvidence?_iff _ _).mp rfl,
          (map_perceiveAtomUnitEvidence_iff _ _).mp rfl,
          evidenceEqual⟩
  · rintro ⟨wellFormed, bondEvidence, atomEvidence,
      bondsJudged, atomsJudged, rfl⟩
    have perceived := (ProductionPerception.perceiveDiagram?_eq_some_iff
      atomCount diagram (ProductionPerception.interpretDiagram diagram)).mpr
      ⟨wellFormed, rfl⟩
    have bondsEqual :=
      (filterMap_perceiveBondUnitEvidence?_iff
        diagram.bonds bondEvidence).mpr bondsJudged
    have atomsEqual :=
      (map_perceiveAtomUnitEvidence_iff
        diagram.atomConfigurations atomEvidence).mpr atomsJudged
    simp [perceiveUnitSpecificDrawing?, perceived, bondsEqual, atomsEqual]

theorem perceiveUnitSpecificDrawing?_eq_none_iff
    (atomCount : Nat) (diagram : DiagramConfiguration) :
    perceiveUnitSpecificDrawing? atomCount diagram = none ↔
      ¬ ProductionPerception.DiagramWellFormed atomCount diagram := by
  by_cases wellFormed : ProductionPerception.DiagramWellFormed atomCount diagram
  · have perceived := (ProductionPerception.perceiveDiagram?_eq_some_iff
      atomCount diagram (ProductionPerception.interpretDiagram diagram)).mpr
      ⟨wellFormed, rfl⟩
    simp [perceiveUnitSpecificDrawing?, perceived, wellFormed]
  · have refused := (ProductionPerception.perceiveDiagram?_eq_none_iff
      atomCount diagram).mpr wellFormed
    simp [perceiveUnitSpecificDrawing?, refused, wellFormed]

end IUPACDrawing2006.UnitSpecificPerception
end TetraStereo.OneCenter
