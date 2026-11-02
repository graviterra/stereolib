import TetraStereo.OneCenter.P93MolecularFullereneRelationalSourceOrientation

set_option autoImplicit false

/-!
# Certified executable relational fullerene program

The independent relational source judgment deliberately uses proposition-valued finite symmetry
semantics.  That is the right specification boundary, but selecting its Boolean substitution test
through `Classical.propDecidable` would make the production program noncomputable.  This module
separates those concerns.  A certified input freezes the already audited five-field test and
carries a proof that it is exactly the relationally derived test.  Runtime evaluation reads only
the frozen data; the proofs connect that computation back to the independent source semantics.
-/

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

/-- A source-oriented relational input with its exact unit ordering and substitution test frozen
as executable data.  The proof fields are not inspected by the runtime analyzer.  `frozenUnit`
also lets a canonical release module expose a plain runtime snapshot which does not retain the
possibly noncomputable proof-carrying source declaration. -/
structure CertifiedRelationalSourceOrientedInput
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration) where
  sourceInput : RelationalSourceOrientedMolecularFullereneConfigurationInput molecule
  frozenUnit : List ℕ
  frozenTest : FullereneSubstitutionTest
  admitted : RelationalSourceOrientedMolecularFullereneConfigurationInputJudgment
    molecule spatial? sourceInput
  testExact :
    deriveMolecularFullereneRelationalSubstitutionTest molecule
        sourceInput.symmetryInput.topologyInput sourceInput.symmetryInput.evidence =
      frozenTest
  unitExact : sourceInput.symmetryInput.topologyInput.carrier.sort (· ≤ ·) = frozenUnit

namespace CertifiedRelationalSourceOrientedInput

/-- The production cage is assembled entirely from finite source data.  In particular, it does
not ask Lean to decide any proposition-valued symmetry judgment at runtime. -/
def executableCage
    {molecule : RawMolecule}
    {spatial? : Option SpatialConfiguration}
    (input : CertifiedRelationalSourceOrientedInput molecule spatial?) :
    MolecularFullereneConfigurationInput :=
  { carrier := input.sourceInput.symmetryInput.topologyInput.carrier
    faces := input.sourceInput.symmetryInput.topologyInput.faces
    substitutionTest := input.frozenTest
    descriptorEvidence := input.sourceInput.symmetryInput.descriptorEvidence }

/-- The frozen executable cage is extensionally the independently derived relational cage. -/
theorem executableCage_eq_sourceCage
    {molecule : RawMolecule}
    {spatial? : Option SpatialConfiguration}
    (input : CertifiedRelationalSourceOrientedInput molecule spatial?) :
    input.executableCage = input.sourceInput.symmetryInput.cage := by
  unfold executableCage
  unfold RelationalSymmetryDerivedMolecularFullereneConfigurationInput.cage
  rw [input.testExact]

/-- Executable spelling of the normalized legacy payload.  Freezing its unit list and spelling
out the remaining field projections isolates the runtime data read by the analyzer from the
proposition-valued source certificate. -/
def executableInput
    {molecule : RawMolecule}
    {spatial? : Option SpatialConfiguration}
    (input : CertifiedRelationalSourceOrientedInput molecule spatial?) :
    FullereneConfigurationInput :=
  { unit := input.frozenUnit
    substitutionTest := input.executableCage.substitutionTest
    descriptorEvidence := input.executableCage.descriptorEvidence }

@[simp] theorem executableInput_eq_toFullereneConfigurationInput
    {molecule : RawMolecule}
    {spatial? : Option SpatialConfiguration}
    (input : CertifiedRelationalSourceOrientedInput molecule spatial?) :
    input.executableInput = input.executableCage.toFullereneConfigurationInput := by
  unfold executableInput MolecularFullereneConfigurationInput.toFullereneConfigurationInput
  unfold executableCage
  rw [input.unitExact]

/-- Admission proves that the executable cage is a checked oriented molecular fullerene map. -/
theorem executableCage_oriented
    {molecule : RawMolecule}
    {spatial? : Option SpatialConfiguration}
    (input : CertifiedRelationalSourceOrientedInput molecule spatial?) :
    OrientedMolecularFullereneFaceMapJudgment molecule input.executableCage := by
  rw [input.executableCage_eq_sourceCage]
  exact input.admitted.relational molecule spatial? input.sourceInput

/-- Hence the runtime cage also satisfies the underlying carrier judgment. -/
theorem executableCage_carrierJudged
    {molecule : RawMolecule}
    {spatial? : Option SpatialConfiguration}
    (input : CertifiedRelationalSourceOrientedInput molecule spatial?) :
    MolecularFullereneCarrierJudgment molecule input.executableCage :=
  input.executableCage_oriented.1

end CertifiedRelationalSourceOrientedInput

/-- Independent complete meaning of output from the certified executable family. -/
def CertifiedRelationalSourceOrientedConfigurationAssignmentJudgment
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (inputs : List (CertifiedRelationalSourceOrientedInput molecule spatial?))
    (assignment : FullereneConfigurationAssignment) : Prop :=
  FullereneConfigurationCandidateJudgment
      (inputs.map CertifiedRelationalSourceOrientedInput.executableInput)
      assignment ∧
    FullereneConfigurationAssignmentAgreement
      (inputs.map CertifiedRelationalSourceOrientedInput.executableInput)
      assignment

/-- Computable production analyzer.  Its data path consists only of `List.map`, the frozen
records, and the existing conflict-aware finite fullerene analyzer. -/
def analyzeCertifiedRelationalSourceOrientedConfigurations
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (inputs : List (CertifiedRelationalSourceOrientedInput molecule spatial?)) :
    List FullereneConfigurationAssignment :=
  analyzeFullereneConfigurations
    (inputs.map CertifiedRelationalSourceOrientedInput.executableInput)

/-- Exact no-invention/no-omission semantics of the computable certified analyzer. -/
theorem mem_analyzeCertifiedRelationalSourceOrientedConfigurations_iff
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (inputs : List (CertifiedRelationalSourceOrientedInput molecule spatial?))
    (assignment : FullereneConfigurationAssignment) :
    assignment ∈ analyzeCertifiedRelationalSourceOrientedConfigurations
        molecule spatial? inputs ↔
      CertifiedRelationalSourceOrientedConfigurationAssignmentJudgment
        molecule spatial? inputs assignment := by
  exact mem_analyzeFullereneConfigurations_iff _ assignment

/-- Certification makes the first independent validation filter extensionally just a map. -/
private theorem validatedRelationalSources_eq_certifiedCages
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (inputs : List (CertifiedRelationalSourceOrientedInput molecule spatial?)) :
    validatedRelationalSourceOrientedMolecularFullereneConfigurationInputs molecule spatial?
        (inputs.map CertifiedRelationalSourceOrientedInput.sourceInput) =
      inputs.map CertifiedRelationalSourceOrientedInput.executableCage := by
  induction inputs with
  | nil => rfl
  | cons input inputs ih =>
      unfold validatedRelationalSourceOrientedMolecularFullereneConfigurationInputs
      unfold validatedRelationalSourceOrientedMolecularFullereneConfigurationInputs at ih
      simp only [List.map_cons, List.filterMap_cons]
      have admittedEq :
          relationalSourceOrientedMolecularFullereneConfigurationInput? molecule spatial?
              input.sourceInput = some input.sourceInput.symmetryInput.cage :=
        (relationalSourceOrientedMolecularFullereneConfigurationInput?_eq_some_iff
          molecule spatial? input.sourceInput input.sourceInput.symmetryInput.cage).2
          ⟨input.admitted, rfl⟩
      rw [admittedEq]
      simp only
      rw [ih, ← input.executableCage_eq_sourceCage]

/-- Certification likewise makes molecular carrier validation extensionally just a map to the
legacy payload consumed by `analyzeFullereneConfigurations`. -/
private theorem validatedCertifiedCages_eq_executableInputs
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (inputs : List (CertifiedRelationalSourceOrientedInput molecule spatial?)) :
    validatedMolecularFullereneConfigurationInputs molecule
        (inputs.map CertifiedRelationalSourceOrientedInput.executableCage) =
      inputs.map CertifiedRelationalSourceOrientedInput.executableInput := by
  induction inputs with
  | nil => rfl
  | cons input inputs ih =>
      unfold validatedMolecularFullereneConfigurationInputs
      unfold validatedMolecularFullereneConfigurationInputs at ih
      simp only [List.map_cons, List.filterMap_cons]
      have admittedEq :
          molecularFullereneConfigurationInput? molecule input.executableCage =
            some input.executableCage.toFullereneConfigurationInput :=
        (molecularFullereneConfigurationInput?_eq_some_iff molecule input.executableCage
          input.executableCage.toFullereneConfigurationInput).2
          ⟨input.executableCage_carrierJudged, rfl⟩
      rw [admittedEq]
      simp only
      rw [ih, ← input.executableInput_eq_toFullereneConfigurationInput]

/-- The constructive frozen program is exactly the existing independent relational analyzer for
the certified source family.  This is full finite-list equality, not merely singleton agreement:
the two proof-carrying admissions discharge both specification-side validation filters. -/
theorem analyzeCertifiedRelationalSourceOrientedConfigurations_eq_relational
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (inputs : List (CertifiedRelationalSourceOrientedInput molecule spatial?)) :
    analyzeCertifiedRelationalSourceOrientedConfigurations molecule spatial? inputs =
      analyzeRelationalSourceOrientedMolecularFullereneConfigurations molecule spatial?
        (inputs.map CertifiedRelationalSourceOrientedInput.sourceInput) := by
  rw [analyzeCertifiedRelationalSourceOrientedConfigurations,
    analyzeRelationalSourceOrientedMolecularFullereneConfigurations,
    analyzeMolecularFullereneConfigurations,
    validatedRelationalSources_eq_certifiedCages,
    validatedCertifiedCages_eq_executableInputs]

/-- Direct bridge from executable membership to the independent relational source judgment. -/
theorem mem_analyzeCertifiedRelationalSourceOrientedConfigurations_iff_relational
    (molecule : RawMolecule)
    (spatial? : Option SpatialConfiguration)
    (inputs : List (CertifiedRelationalSourceOrientedInput molecule spatial?))
    (assignment : FullereneConfigurationAssignment) :
    assignment ∈ analyzeCertifiedRelationalSourceOrientedConfigurations
        molecule spatial? inputs ↔
      RelationalSourceOrientedMolecularFullereneConfigurationAssignmentJudgment molecule
        spatial? (inputs.map CertifiedRelationalSourceOrientedInput.sourceInput) assignment := by
  rw [analyzeCertifiedRelationalSourceOrientedConfigurations_eq_relational,
    mem_analyzeRelationalSourceOrientedMolecularFullereneConfigurations_iff]

end BlueBookP93.Cyclic
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.CertifiedRelationalSourceOrientedInput.executableCage_eq_sourceCage
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.mem_analyzeCertifiedRelationalSourceOrientedConfigurations_iff
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.analyzeCertifiedRelationalSourceOrientedConfigurations_eq_relational
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.mem_analyzeCertifiedRelationalSourceOrientedConfigurations_iff_relational
