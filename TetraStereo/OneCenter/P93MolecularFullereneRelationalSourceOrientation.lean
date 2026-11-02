import TetraStereo.OneCenter.P93MolecularFullereneRelationalSymmetry
import TetraStereo.OneCenter.P93MolecularFullereneSourceOrientation

set_option autoImplicit false

/-!
# Source orientation for graph-backed fullerene substitution evidence

This is the source-complete boundary used by concrete fullerene derivatives.  It combines the
relational, molecule-indexed substitution judgment with either exact supporting coordinates or
an independently oriented exterior surface.  The output forgets the proof packaging and retains
the checked molecular cage, so the existing conflict-aware P-93.5.6 analyzer can consume an
entire family without a second hand-written bridge.
-/

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

noncomputable section

/-- A graph-backed substitution source together with the evidence determining the printed
numbering turn. -/
structure RelationalSourceOrientedMolecularFullereneConfigurationInput
    (molecule : RawMolecule) where
  symmetryInput : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule
  numberingEvidence : MolecularFullereneNumberingEvidence
  turnSource : MolecularFullereneSourceTurn

/-- Exact admission boundary.  Both branches retain the full graph-backed substitution judgment.
The exterior branch remains meaningful without coordinates and, when coordinates are present,
requires their supporting-plane turn to agree with the exterior turn. -/
def RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (input : RelationalSourceOrientedMolecularFullereneConfigurationInput molecule) : Prop :=
  match input.turnSource with
  | .supportingSpatial =>
      ∃ spatial,
        spatial? = some spatial ∧
          RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment
            molecule input.symmetryInput ∧
          ∃ turn,
            MolecularFullereneThreeLocantTurnJudgment spatial input.symmetryInput.cage
                input.numberingEvidence turn ∧
              input.symmetryInput.cage.descriptorEvidence.cageNumberingKind =
                some input.numberingEvidence.numberingKind ∧
              input.symmetryInput.cage.descriptorEvidence.cageTurn = some turn
  | .exterior sense =>
      RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment
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

noncomputable instance relationalSourceOrientedInputJudgmentDecidable
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (input : RelationalSourceOrientedMolecularFullereneConfigurationInput molecule) :
    Decidable (RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment
      molecule spatial? input) := Classical.propDecidable _

/-- Either admissible turn source retains the same graph-backed substitution judgment. -/
theorem RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment.relational
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (input : RelationalSourceOrientedMolecularFullereneConfigurationInput molecule)
    (judged : RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment
      molecule spatial? input) :
    RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment
      molecule input.symmetryInput := by
  cases sourceEq : input.turnSource with
  | supportingSpatial =>
      rw [RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment,
        sourceEq] at judged
      exact judged.choose_spec.2.1
  | exterior sense =>
      rw [RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment,
        sourceEq] at judged
      exact judged.1

/-- The coordinate-backed specialization exposes precisely the relational substitution judgment,
the independent three-locant turn, and exact descriptor agreement. -/
@[simp] theorem relationalSourceOriented_supportingSpatial_judgment_iff
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (symmetryInput : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule)
    (numberingEvidence : MolecularFullereneNumberingEvidence) :
    RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment molecule (some spatial)
        { symmetryInput := symmetryInput
          numberingEvidence := numberingEvidence
          turnSource := .supportingSpatial } ↔
      RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment molecule symmetryInput ∧
        ∃ turn,
          MolecularFullereneThreeLocantTurnJudgment spatial symmetryInput.cage
              numberingEvidence turn ∧
            symmetryInput.cage.descriptorEvidence.cageNumberingKind =
              some numberingEvidence.numberingKind ∧
            symmetryInput.cage.descriptorEvidence.cageTurn = some turn := by
  simp [RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment]

/-- With coordinates, the exterior branch includes the exact consistency condition against the
supporting-plane construction. -/
@[simp] theorem relationalSourceOriented_exterior_judgment_some_iff
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (symmetryInput : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule)
    (numberingEvidence : MolecularFullereneNumberingEvidence)
    (sense : FullereneExteriorFaceSense) :
    RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment molecule (some spatial)
        { symmetryInput := symmetryInput
          numberingEvidence := numberingEvidence
          turnSource := .exterior sense } ↔
      RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment molecule symmetryInput ∧
        ∃ turn,
          MolecularFullereneExteriorTurnJudgment molecule symmetryInput.cage
              numberingEvidence sense turn ∧
            symmetryInput.cage.descriptorEvidence.cageNumberingKind =
              some numberingEvidence.numberingKind ∧
            symmetryInput.cage.descriptorEvidence.cageTurn = some turn ∧
            ∀ supportingTurn,
              MolecularFullereneThreeLocantTurnJudgment spatial symmetryInput.cage
                  numberingEvidence supportingTurn →
                supportingTurn = turn := by
  simp only [RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment]
  constructor
  · rintro ⟨relational, turn, exterior, numberingEq, turnEq, agreement⟩
    exact ⟨relational, turn, exterior, numberingEq, turnEq,
      fun supportingTurn supporting => agreement spatial supportingTurn rfl supporting⟩
  · rintro ⟨relational, turn, exterior, numberingEq, turnEq, agreement⟩
    refine ⟨relational, turn, exterior, numberingEq, turnEq, ?_⟩
    intro candidateSpatial supportingTurn spatialEq supporting
    cases spatialEq
    exact agreement supportingTurn supporting

/-- Without coordinates the exterior route is still exact and does not invent spatial data. -/
@[simp] theorem relationalSourceOriented_exterior_judgment_none_iff
    (molecule : RawMolecule)
    (symmetryInput : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule)
    (numberingEvidence : MolecularFullereneNumberingEvidence)
    (sense : FullereneExteriorFaceSense) :
    RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment molecule none
        { symmetryInput := symmetryInput
          numberingEvidence := numberingEvidence
          turnSource := .exterior sense } ↔
      RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment molecule symmetryInput ∧
        ∃ turn,
          MolecularFullereneExteriorTurnJudgment molecule symmetryInput.cage
              numberingEvidence sense turn ∧
            symmetryInput.cage.descriptorEvidence.cageNumberingKind =
              some numberingEvidence.numberingKind ∧
            symmetryInput.cage.descriptorEvidence.cageTurn = some turn := by
  simp [RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment]

/-- Admit a source only after the relational substitution and orientation witnesses agree. -/
noncomputable def relationalSourceOrientedMolecularFullereneConfigurationInput?
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (input : RelationalSourceOrientedMolecularFullereneConfigurationInput molecule) :
    Option MolecularFullereneConfigurationInput :=
  if RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment
      molecule spatial? input then
    some input.symmetryInput.cage
  else none

@[simp] theorem relationalSourceOrientedMolecularFullereneConfigurationInput?_eq_some_iff
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (input : RelationalSourceOrientedMolecularFullereneConfigurationInput molecule)
    (cage : MolecularFullereneConfigurationInput) :
    relationalSourceOrientedMolecularFullereneConfigurationInput? molecule spatial? input =
        some cage ↔
      RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment
          molecule spatial? input ∧
        cage = input.symmetryInput.cage := by
  by_cases valid : RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment
      molecule spatial? input
  · simp [relationalSourceOrientedMolecularFullereneConfigurationInput?, valid, eq_comm]
  · simp [relationalSourceOrientedMolecularFullereneConfigurationInput?, valid]

@[simp] theorem relationalSourceOrientedMolecularFullereneConfigurationInput?_eq_none_iff
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (input : RelationalSourceOrientedMolecularFullereneConfigurationInput molecule) :
    relationalSourceOrientedMolecularFullereneConfigurationInput? molecule spatial? input = none ↔
      ¬RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment
        molecule spatial? input := by
  by_cases valid : RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment
      molecule spatial? input
  · simp [relationalSourceOrientedMolecularFullereneConfigurationInput?, valid]
  · simp [relationalSourceOrientedMolecularFullereneConfigurationInput?, valid]

/-- All and only graph-backed source records admitted by their declared turn source. -/
noncomputable def validatedRelationalSourceOrientedMolecularFullereneConfigurationInputs
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (inputs : List (RelationalSourceOrientedMolecularFullereneConfigurationInput molecule)) :
    List MolecularFullereneConfigurationInput :=
  inputs.filterMap
    (relationalSourceOrientedMolecularFullereneConfigurationInput? molecule spatial?)

theorem mem_validatedRelationalSourceOrientedMolecularFullereneConfigurationInputs_iff
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (inputs : List (RelationalSourceOrientedMolecularFullereneConfigurationInput molecule))
    (cage : MolecularFullereneConfigurationInput) :
    cage ∈ validatedRelationalSourceOrientedMolecularFullereneConfigurationInputs
        molecule spatial? inputs ↔
      ∃ input ∈ inputs,
        RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment
            molecule spatial? input ∧
          cage = input.symmetryInput.cage := by
  simp [validatedRelationalSourceOrientedMolecularFullereneConfigurationInputs,
    relationalSourceOrientedMolecularFullereneConfigurationInput?_eq_some_iff]

/-- Independent complete meaning of an assignment originating at the relational source boundary. -/
def RelationalSourceOrientedMolecularFullereneConfigurationAssignmentJudgment
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (inputs : List (RelationalSourceOrientedMolecularFullereneConfigurationInput molecule))
    (assignment : FullereneConfigurationAssignment) : Prop :=
  ∃ input ∈ inputs,
    RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment molecule spatial? input ∧
      FullereneConfigurationAssignmentJudgment
        input.symmetryInput.cage.toFullereneConfigurationInput assignment ∧
      FullereneConfigurationAssignmentAgreement
        (validatedMolecularFullereneConfigurationInputs molecule
          (validatedRelationalSourceOrientedMolecularFullereneConfigurationInputs
            molecule spatial? inputs))
        assignment

/-- The source-level assignment judgment is exactly the existing molecular judgment over the
admitted cage projections. -/
theorem relationalSourceOrientedMolecularFullereneConfigurationAssignmentJudgment_iff_molecular
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (inputs : List (RelationalSourceOrientedMolecularFullereneConfigurationInput molecule))
    (assignment : FullereneConfigurationAssignment) :
    RelationalSourceOrientedMolecularFullereneConfigurationAssignmentJudgment
        molecule spatial? inputs assignment ↔
      MolecularFullereneConfigurationAssignmentJudgment molecule
        (validatedRelationalSourceOrientedMolecularFullereneConfigurationInputs
          molecule spatial? inputs)
        assignment := by
  unfold RelationalSourceOrientedMolecularFullereneConfigurationAssignmentJudgment
  unfold MolecularFullereneConfigurationAssignmentJudgment
  constructor
  · rintro ⟨input, inputPresent, sourceJudged, localJudged, agreement⟩
    exact ⟨input.symmetryInput.cage,
      (mem_validatedRelationalSourceOrientedMolecularFullereneConfigurationInputs_iff
        molecule spatial? inputs input.symmetryInput.cage).mpr
          ⟨input, inputPresent, sourceJudged, rfl⟩,
      (sourceJudged.relational molecule spatial? input).1, localJudged, agreement⟩
  · rintro ⟨cage, cagePresent, _carrierJudged, localJudged, agreement⟩
    rcases (mem_validatedRelationalSourceOrientedMolecularFullereneConfigurationInputs_iff
      molecule spatial? inputs cage).mp cagePresent with
      ⟨input, inputPresent, sourceJudged, cageEq⟩
    subst cage
    exact ⟨input, inputPresent, sourceJudged, localJudged, agreement⟩

/-- A single locally admitted relational source with one locally judged assignment already
satisfies the analyzer's complete assignment judgment.  Family agreement is not an extra
row-authored witness: both validation layers reduce any competing candidate to the same cage
input, and local assignment functionality forces equality.  Source-policy authorization remains
a separate authority-observation obligation. -/
theorem relationalSourceOrientedMolecularFullereneConfigurationAssignmentJudgment_singleton
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (input : RelationalSourceOrientedMolecularFullereneConfigurationInput molecule)
    (assignment : FullereneConfigurationAssignment)
    (sourceJudged : RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment
      molecule spatial? input)
    (localJudged : FullereneConfigurationAssignmentJudgment
      input.symmetryInput.cage.toFullereneConfigurationInput assignment) :
    RelationalSourceOrientedMolecularFullereneConfigurationAssignmentJudgment
      molecule spatial? [input] assignment := by
  refine ⟨input, by simp, sourceJudged, localJudged, ?_⟩
  intro other candidate _sameUnit
  rcases candidate with ⟨legacy, legacyPresent, otherJudged⟩
  rcases (mem_validatedMolecularFullereneConfigurationInputs_iff molecule
      (validatedRelationalSourceOrientedMolecularFullereneConfigurationInputs
        molecule spatial? [input]) legacy).1 legacyPresent with
    ⟨cage, cagePresent, _carrierJudged, legacyEq⟩
  rcases (mem_validatedRelationalSourceOrientedMolecularFullereneConfigurationInputs_iff
      molecule spatial? [input] cage).1 cagePresent with
    ⟨selected, selectedPresent, _selectedJudged, cageEq⟩
  simp only [List.mem_singleton] at selectedPresent
  subst selected
  subst cage
  subst legacy
  exact fullereneConfigurationAssignmentJudgment_subsingleton
    input.symmetryInput.cage.toFullereneConfigurationInput otherJudged localJudged

/-- Run the complete conflict-aware P-93.5.6 analyzer directly from relational source records. -/
noncomputable def analyzeRelationalSourceOrientedMolecularFullereneConfigurations
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (inputs : List (RelationalSourceOrientedMolecularFullereneConfigurationInput molecule)) :
    List FullereneConfigurationAssignment :=
  analyzeMolecularFullereneConfigurations molecule
    (validatedRelationalSourceOrientedMolecularFullereneConfigurationInputs
      molecule spatial? inputs)

/-- Exact no-invention/no-omission semantics for the complete relational source analyzer. -/
theorem mem_analyzeRelationalSourceOrientedMolecularFullereneConfigurations_iff
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (inputs : List (RelationalSourceOrientedMolecularFullereneConfigurationInput molecule))
    (assignment : FullereneConfigurationAssignment) :
    assignment ∈ analyzeRelationalSourceOrientedMolecularFullereneConfigurations
        molecule spatial? inputs ↔
      RelationalSourceOrientedMolecularFullereneConfigurationAssignmentJudgment
        molecule spatial? inputs assignment := by
  rw [analyzeRelationalSourceOrientedMolecularFullereneConfigurations,
    mem_analyzeMolecularFullereneConfigurations_iff,
    ← relationalSourceOrientedMolecularFullereneConfigurationAssignmentJudgment_iff_molecular]

end

end BlueBookP93.Cyclic
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.relationalSourceOrientedMolecularFullereneConfigurationInput?_eq_some_iff
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.relationalSourceOrientedMolecularFullereneConfigurationAssignmentJudgment_iff_molecular
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.mem_analyzeRelationalSourceOrientedMolecularFullereneConfigurations_iff
