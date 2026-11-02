import TetraStereo.OneCenter.P93MolecularFullereneExteriorOrientation

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

noncomputable section

/-!
# Source-complete orientation for molecular fullerene numbering

The printed P-93.5.6 orientation of locants 1→2→3 can be justified in either of the two
ways actually available from an authoritative source.  Exact supporting coordinates use the
existing spatial judgment.  A source without such coordinates instead carries the outside sense
of its coherently oriented fullerene surface and uses the independent exterior-turn judgment.

The exterior route is not allowed to contradict coordinates when they are present: every turn
which the stronger supporting-plane judgment can derive must equal the exterior-derived turn.
Thus this layer removes a spatial-data requirement, not a mathematical requirement.
-/

/-- The authoritative source of the clockwise/anticlockwise fullerene numbering turn. -/
inductive MolecularFullereneSourceTurn where
  | supportingSpatial
  | exterior (sense : FullereneExteriorFaceSense)
  deriving DecidableEq, Repr

/-- Temporary common source record used while the canonical observations migrate from their
spatial-only representation. -/
structure SourceOrientedMolecularFullereneConfigurationInput where
  symmetryInput : SymmetryDerivedMolecularFullereneConfigurationInput
  numberingEvidence : MolecularFullereneNumberingEvidence
  turnSource : MolecularFullereneSourceTurn

namespace SourceOrientedMolecularFullereneConfigurationInput

/-- Forget only the choice of turn source. -/
def toSpatiallyDerived
    (input : SourceOrientedMolecularFullereneConfigurationInput) :
    SpatiallyDerivedMolecularFullereneConfigurationInput where
  symmetryInput := input.symmetryInput
  numberingEvidence := input.numberingEvidence

/-- Interpret an exterior source record in the already established exterior layer. -/
def toExteriorDerived
    (input : SourceOrientedMolecularFullereneConfigurationInput)
    (sense : FullereneExteriorFaceSense) :
    ExteriorDerivedMolecularFullereneConfigurationInput where
  symmetryInput := input.symmetryInput
  numberingEvidence := input.numberingEvidence
  exteriorSense := sense

end SourceOrientedMolecularFullereneConfigurationInput

/-- Exact common admission boundary for source-derived molecular fullerene orientation.

The spatial branch is literally the old spatial judgment plus evidence that the requested spatial
record is present.  The exterior branch uses the independent surface judgment and requires
descriptor agreement.  Its final clause is vacuous only when the authoritative source has no
coordinates; if coordinates are present, every supporting-plane turn they derive must agree. -/
def SourceOrientedMolecularFullereneConfigurationInputJudgment
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (input : SourceOrientedMolecularFullereneConfigurationInput) : Prop :=
  match input.turnSource with
  | .supportingSpatial =>
      ∃ spatial,
        spatial? = some spatial ∧
          SpatiallyDerivedMolecularFullereneConfigurationInputJudgment
            molecule spatial input.toSpatiallyDerived
  | .exterior sense =>
      SymmetryDerivedMolecularFullereneConfigurationInputJudgment
          molecule input.symmetryInput ∧
        ∃ turn,
          MolecularFullereneExteriorTurnJudgment molecule input.symmetryInput.cage
              input.numberingEvidence sense turn ∧
            input.symmetryInput.cage.descriptorEvidence.cageNumberingKind =
              some input.numberingEvidence.numberingKind ∧
            input.symmetryInput.cage.descriptorEvidence.cageTurn = some turn ∧
            ∀ spatial supportingTurn,
              spatial? = some spatial →
                MolecularFullereneThreeLocantTurnJudgment spatial input.symmetryInput.cage
                    input.numberingEvidence supportingTurn →
                  supportingTurn = turn

noncomputable instance sourceOrientedMolecularFullereneConfigurationInputJudgmentDecidable
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (input : SourceOrientedMolecularFullereneConfigurationInput) :
    Decidable (SourceOrientedMolecularFullereneConfigurationInputJudgment
      molecule spatial? input) :=
  Classical.propDecidable _

/-- Every admitted common source record projects to a valid symmetry-derived input. -/
theorem SourceOrientedMolecularFullereneConfigurationInputJudgment.symmetry
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (input : SourceOrientedMolecularFullereneConfigurationInput)
    (judged : SourceOrientedMolecularFullereneConfigurationInputJudgment
      molecule spatial? input) :
    SymmetryDerivedMolecularFullereneConfigurationInputJudgment
      molecule input.symmetryInput := by
  cases sourceEq : input.turnSource with
  | supportingSpatial =>
      rw [SourceOrientedMolecularFullereneConfigurationInputJudgment,
        sourceEq] at judged
      rcases judged with ⟨spatial, _spatialPresent, spatialJudged⟩
      exact spatialJudged.1
  | exterior sense =>
      rw [SourceOrientedMolecularFullereneConfigurationInputJudgment,
        sourceEq] at judged
      exact judged.1

/-- With a present spatial record, the supporting-spatial specialization is exactly the existing
strict spatial judgment. -/
@[simp] theorem sourceOriented_supportingSpatial_judgment_iff
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (symmetryInput : SymmetryDerivedMolecularFullereneConfigurationInput)
    (numberingEvidence : MolecularFullereneNumberingEvidence) :
    SourceOrientedMolecularFullereneConfigurationInputJudgment molecule (some spatial)
        { symmetryInput := symmetryInput
          numberingEvidence := numberingEvidence
          turnSource := .supportingSpatial } ↔
      SpatiallyDerivedMolecularFullereneConfigurationInputJudgment molecule spatial
        { symmetryInput := symmetryInput
          numberingEvidence := numberingEvidence } := by
  simp [SourceOrientedMolecularFullereneConfigurationInputJudgment,
    SourceOrientedMolecularFullereneConfigurationInput.toSpatiallyDerived]

/-- With present coordinates, the exterior specialization is exactly the established exterior
judgment. -/
@[simp] theorem sourceOriented_exterior_judgment_some_iff
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (symmetryInput : SymmetryDerivedMolecularFullereneConfigurationInput)
    (numberingEvidence : MolecularFullereneNumberingEvidence)
    (sense : FullereneExteriorFaceSense) :
    SourceOrientedMolecularFullereneConfigurationInputJudgment molecule (some spatial)
        { symmetryInput := symmetryInput
          numberingEvidence := numberingEvidence
          turnSource := .exterior sense } ↔
      ExteriorDerivedMolecularFullereneConfigurationInputJudgment molecule spatial
        { symmetryInput := symmetryInput
          numberingEvidence := numberingEvidence
          exteriorSense := sense } := by
  simp only [SourceOrientedMolecularFullereneConfigurationInputJudgment,
    ExteriorDerivedMolecularFullereneConfigurationInputJudgment]
  constructor
  · rintro ⟨symmetryJudged, turn, exteriorJudged, numberingEq, turnEq, agreement⟩
    exact ⟨symmetryJudged, turn, exteriorJudged, numberingEq, turnEq,
      fun supportingTurn supportingJudged =>
        agreement spatial supportingTurn rfl supportingJudged⟩
  · rintro ⟨symmetryJudged, turn, exteriorJudged, numberingEq, turnEq, agreement⟩
    refine ⟨symmetryJudged, turn, exteriorJudged, numberingEq, turnEq, ?_⟩
    intro candidateSpatial supportingTurn spatialPresent supportingJudged
    cases spatialPresent
    exact agreement supportingTurn supportingJudged

/-- An exterior source remains admissible without invented coordinates; all geometric and
descriptor claims are still checked by the exterior and symmetry judgments. -/
@[simp] theorem sourceOriented_exterior_judgment_none_iff
    (molecule : RawMolecule)
    (symmetryInput : SymmetryDerivedMolecularFullereneConfigurationInput)
    (numberingEvidence : MolecularFullereneNumberingEvidence)
    (sense : FullereneExteriorFaceSense) :
    SourceOrientedMolecularFullereneConfigurationInputJudgment molecule none
        { symmetryInput := symmetryInput
          numberingEvidence := numberingEvidence
          turnSource := .exterior sense } ↔
      SymmetryDerivedMolecularFullereneConfigurationInputJudgment molecule symmetryInput ∧
        ∃ turn,
          MolecularFullereneExteriorTurnJudgment molecule symmetryInput.cage
              numberingEvidence sense turn ∧
            symmetryInput.cage.descriptorEvidence.cageNumberingKind =
              some numberingEvidence.numberingKind ∧
            symmetryInput.cage.descriptorEvidence.cageTurn = some turn := by
  simp [SourceOrientedMolecularFullereneConfigurationInputJudgment]

/-- Boolean admission checker for callers which need only acceptance or refusal. -/
noncomputable def sourceOrientedMolecularFullereneConfigurationInputAccepted?
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (input : SourceOrientedMolecularFullereneConfigurationInput) : Bool :=
  decide (SourceOrientedMolecularFullereneConfigurationInputJudgment
    molecule spatial? input)

@[simp] theorem sourceOrientedMolecularFullereneConfigurationInputAccepted?_eq_true_iff
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (input : SourceOrientedMolecularFullereneConfigurationInput) :
    sourceOrientedMolecularFullereneConfigurationInputAccepted? molecule spatial? input = true ↔
      SourceOrientedMolecularFullereneConfigurationInputJudgment
        molecule spatial? input := by
  simp [sourceOrientedMolecularFullereneConfigurationInputAccepted?]

/-- Exact checked projection to the symmetry-derived layer. -/
noncomputable def sourceOrientedMolecularFullereneConfigurationInput?
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (input : SourceOrientedMolecularFullereneConfigurationInput) :
    Option SymmetryDerivedMolecularFullereneConfigurationInput :=
  if SourceOrientedMolecularFullereneConfigurationInputJudgment molecule spatial? input then
    some input.symmetryInput
  else
    none

@[simp] theorem sourceOrientedMolecularFullereneConfigurationInput?_eq_some_iff
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (input : SourceOrientedMolecularFullereneConfigurationInput)
    (symmetryInput : SymmetryDerivedMolecularFullereneConfigurationInput) :
    sourceOrientedMolecularFullereneConfigurationInput? molecule spatial? input =
        some symmetryInput ↔
      SourceOrientedMolecularFullereneConfigurationInputJudgment molecule spatial? input ∧
        symmetryInput = input.symmetryInput := by
  by_cases valid : SourceOrientedMolecularFullereneConfigurationInputJudgment
      molecule spatial? input
  · simp [sourceOrientedMolecularFullereneConfigurationInput?, valid, eq_comm]
  · simp [sourceOrientedMolecularFullereneConfigurationInput?, valid]

@[simp] theorem sourceOrientedMolecularFullereneConfigurationInput?_eq_none_iff
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (input : SourceOrientedMolecularFullereneConfigurationInput) :
    sourceOrientedMolecularFullereneConfigurationInput? molecule spatial? input = none ↔
      ¬SourceOrientedMolecularFullereneConfigurationInputJudgment molecule spatial? input := by
  by_cases valid : SourceOrientedMolecularFullereneConfigurationInputJudgment
      molecule spatial? input
  · simp [sourceOrientedMolecularFullereneConfigurationInput?, valid]
  · simp [sourceOrientedMolecularFullereneConfigurationInput?, valid]

/-- All and only common source records admitted by their declared turn source. -/
noncomputable def validatedSourceOrientedMolecularFullereneConfigurationInputs
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (inputs : List SourceOrientedMolecularFullereneConfigurationInput) :
    List SymmetryDerivedMolecularFullereneConfigurationInput :=
  inputs.filterMap
    (sourceOrientedMolecularFullereneConfigurationInput? molecule spatial?)

/-- Exact finite-family membership at the common source-orientation boundary. -/
theorem mem_validatedSourceOrientedMolecularFullereneConfigurationInputs_iff
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (inputs : List SourceOrientedMolecularFullereneConfigurationInput)
    (symmetryInput : SymmetryDerivedMolecularFullereneConfigurationInput) :
    symmetryInput ∈
        validatedSourceOrientedMolecularFullereneConfigurationInputs
          molecule spatial? inputs ↔
      ∃ input ∈ inputs,
        SourceOrientedMolecularFullereneConfigurationInputJudgment
            molecule spatial? input ∧
          symmetryInput = input.symmetryInput := by
  simp [validatedSourceOrientedMolecularFullereneConfigurationInputs,
    sourceOrientedMolecularFullereneConfigurationInput?_eq_some_iff]

/-- Independent meaning of a family assignment from the common source-orientation boundary. -/
def SourceOrientedMolecularFullereneConfigurationAssignmentJudgment
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (inputs : List SourceOrientedMolecularFullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment) : Prop :=
  ∃ input ∈ inputs,
    SourceOrientedMolecularFullereneConfigurationInputJudgment molecule spatial? input ∧
      FullereneConfigurationAssignmentJudgment
        input.symmetryInput.cage.toFullereneConfigurationInput assignment ∧
      FullereneConfigurationAssignmentAgreement
        (validatedMolecularFullereneConfigurationInputs molecule
          (validatedSymmetryDerivedMolecularFullereneConfigurationInputs molecule
            (validatedSourceOrientedMolecularFullereneConfigurationInputs
              molecule spatial? inputs)))
        assignment

/-- The common source judgment is exactly the symmetry-backed assignment judgment over the
admitted projections. -/
theorem sourceOrientedMolecularFullereneConfigurationAssignmentJudgment_iff_symmetry
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (inputs : List SourceOrientedMolecularFullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment) :
    SourceOrientedMolecularFullereneConfigurationAssignmentJudgment
        molecule spatial? inputs assignment ↔
      SymmetryDerivedMolecularFullereneConfigurationAssignmentJudgment molecule
        (validatedSourceOrientedMolecularFullereneConfigurationInputs
          molecule spatial? inputs)
        assignment := by
  unfold SourceOrientedMolecularFullereneConfigurationAssignmentJudgment
  unfold SymmetryDerivedMolecularFullereneConfigurationAssignmentJudgment
  constructor
  · rintro ⟨input, inputPresent, sourceJudged, localJudged, agreement⟩
    exact ⟨input.symmetryInput,
      (mem_validatedSourceOrientedMolecularFullereneConfigurationInputs_iff
        molecule spatial? inputs input.symmetryInput).mpr
          ⟨input, inputPresent, sourceJudged, rfl⟩,
      sourceJudged.symmetry molecule spatial? input,
      localJudged, agreement⟩
  · rintro ⟨symmetryInput, symmetryPresent, _symmetryJudged, localJudged, agreement⟩
    rcases (mem_validatedSourceOrientedMolecularFullereneConfigurationInputs_iff
      molecule spatial? inputs symmetryInput).mp symmetryPresent with
      ⟨input, inputPresent, sourceJudged, symmetryEq⟩
    subst symmetryInput
    exact ⟨input, inputPresent, sourceJudged, localJudged, agreement⟩

/-- Run the complete conflict-aware fullerene analyzer after common source-orientation admission. -/
noncomputable def analyzeSourceOrientedMolecularFullereneConfigurations
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (inputs : List SourceOrientedMolecularFullereneConfigurationInput) :
    List FullereneConfigurationAssignment :=
  analyzeMolecularFullereneConfigurations molecule
    (validatedSymmetryDerivedMolecularFullereneConfigurationInputs molecule
      (validatedSourceOrientedMolecularFullereneConfigurationInputs
        molecule spatial? inputs))

/-- The common analyzer has exact no-invention/no-omission family semantics. -/
theorem mem_analyzeSourceOrientedMolecularFullereneConfigurations_iff
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (inputs : List SourceOrientedMolecularFullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment) :
    assignment ∈
        analyzeSourceOrientedMolecularFullereneConfigurations molecule spatial? inputs ↔
      SourceOrientedMolecularFullereneConfigurationAssignmentJudgment
        molecule spatial? inputs assignment := by
  rw [analyzeSourceOrientedMolecularFullereneConfigurations,
    mem_analyzeMolecularFullereneConfigurations_iff,
    ← symmetryDerivedMolecularFullereneConfigurationAssignmentJudgment_iff_molecular,
    ← sourceOrientedMolecularFullereneConfigurationAssignmentJudgment_iff_symmetry]

end

end BlueBookP93.Cyclic
end TetraStereo.OneCenter
