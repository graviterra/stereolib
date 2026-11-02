import TetraStereo.OneCenter.P93MolecularFullereneRelationalSymmetry

set_option autoImplicit false

/-!
# Certified executable symmetry-only relational fullerene program

Some P-93.5.6 rows, notably the printed Type 4 example, carry no cage-numbering or turn
descriptor.  Requiring a source-orientation record for such a row would invent evidence.  This
module therefore supplies the parallel boundary that stops exactly at the independently checked
relational symmetry input.

Runtime data and specification data are deliberately separate.  A frozen snapshot contains only
the ascending carrier enumeration, the five-field substitution test, and descriptor evidence.
The certificate relates that snapshot to a graph-backed relational source and is never needed to
evaluate the production analyzer.
-/

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

/-- Complete finite runtime payload for one symmetry-derived fullerene classification. -/
structure FrozenRelationalSymmetryRuntimeInput where
  carrier : List ℕ
  substitutionTest : FullereneSubstitutionTest
  descriptorEvidence : FullereneDescriptorEvidence

namespace FrozenRelationalSymmetryRuntimeInput

/-- Direct input to the existing complete conflict-aware fullerene analyzer. -/
def toFullereneConfigurationInput
    (input : FrozenRelationalSymmetryRuntimeInput) : FullereneConfigurationInput :=
  { unit := input.carrier
    substitutionTest := input.substitutionTest
    descriptorEvidence := input.descriptorEvidence }

end FrozenRelationalSymmetryRuntimeInput

/-- Proof-only bridge from one frozen runtime snapshot to one independently admitted relational
symmetry source. -/
structure CertifiedRelationalSymmetryInput (molecule : RawMolecule) where
  sourceInput : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule
  runtimeInput : FrozenRelationalSymmetryRuntimeInput
  admitted : RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment
    molecule sourceInput
  carrierExact : sourceInput.topologyInput.carrier.sort (· ≤ ·) = runtimeInput.carrier
  testExact :
    deriveMolecularFullereneRelationalSubstitutionTest molecule
        sourceInput.topologyInput sourceInput.evidence =
      runtimeInput.substitutionTest
  descriptorExact : sourceInput.descriptorEvidence = runtimeInput.descriptorEvidence

namespace CertifiedRelationalSymmetryInput

/-- Every runtime field is exactly the canonical legacy projection of the relational source. -/
theorem runtimeInput_eq_sourceInput
    {molecule : RawMolecule}
    (input : CertifiedRelationalSymmetryInput molecule) :
    input.runtimeInput.toFullereneConfigurationInput =
      input.sourceInput.cage.toFullereneConfigurationInput := by
  unfold FrozenRelationalSymmetryRuntimeInput.toFullereneConfigurationInput
    MolecularFullereneConfigurationInput.toFullereneConfigurationInput
    RelationalSymmetryDerivedMolecularFullereneConfigurationInput.cage
  rw [input.carrierExact, input.testExact, input.descriptorExact]

/-- Admission includes the molecular carrier judgment used by the second validation boundary. -/
theorem sourceCage_carrierJudged
    {molecule : RawMolecule}
    (input : CertifiedRelationalSymmetryInput molecule) :
    MolecularFullereneCarrierJudgment molecule input.sourceInput.cage :=
  input.admitted.1

end CertifiedRelationalSymmetryInput

/-! ## Independent symmetry-only analyzer semantics -/

/-- Independent assignment meaning after relational-symmetry admission and molecular carrier
validation.  No numbering or exterior-turn proposition occurs in this judgment. -/
def RelationalSymmetryDerivedMolecularFullereneConfigurationAssignmentJudgment
    (molecule : RawMolecule)
    (sources : List (RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule))
    (assignment : FullereneConfigurationAssignment) : Prop :=
  MolecularFullereneConfigurationAssignmentJudgment molecule
    (validatedRelationalSymmetryDerivedMolecularFullereneConfigurationInputs molecule sources)
    assignment

/-- Specification analyzer for symmetry-only graph sources.  It remains noncomputable because
source admission is proposition-valued; the frozen production analyzer below is executable. -/
noncomputable def analyzeRelationalSymmetryDerivedMolecularFullereneConfigurations
    (molecule : RawMolecule)
    (sources : List (RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule)) :
    List FullereneConfigurationAssignment :=
  analyzeMolecularFullereneConfigurations molecule
    (validatedRelationalSymmetryDerivedMolecularFullereneConfigurationInputs molecule sources)

/-- Exact no-invention/no-omission membership of the independent symmetry-only analyzer. -/
theorem mem_analyzeRelationalSymmetryDerivedMolecularFullereneConfigurations_iff
    (molecule : RawMolecule)
    (sources : List (RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule))
    (assignment : FullereneConfigurationAssignment) :
    assignment ∈ analyzeRelationalSymmetryDerivedMolecularFullereneConfigurations
        molecule sources ↔
      RelationalSymmetryDerivedMolecularFullereneConfigurationAssignmentJudgment
        molecule sources assignment := by
  exact mem_analyzeMolecularFullereneConfigurations_iff _ _ assignment

/-! ## Fully computable frozen production analyzer -/

/-- Production computation over frozen data only. -/
def analyzeFrozenRelationalSymmetryConfigurations
    (inputs : List FrozenRelationalSymmetryRuntimeInput) :
    List FullereneConfigurationAssignment :=
  analyzeFullereneConfigurations
    (inputs.map FrozenRelationalSymmetryRuntimeInput.toFullereneConfigurationInput)

/-- Exact finite-family meaning of membership in the frozen runtime output. -/
theorem mem_analyzeFrozenRelationalSymmetryConfigurations_iff
    (inputs : List FrozenRelationalSymmetryRuntimeInput)
    (assignment : FullereneConfigurationAssignment) :
    assignment ∈ analyzeFrozenRelationalSymmetryConfigurations inputs ↔
      ConflictFreeFullereneConfigurationAssignmentJudgment
        (inputs.map FrozenRelationalSymmetryRuntimeInput.toFullereneConfigurationInput)
        assignment := by
  exact mem_analyzeFullereneConfigurations_iff _ assignment

/-! ## Certificate transport -/

private theorem validatedRelationalSymmetrySources_eq_sourceCages
    (molecule : RawMolecule)
    (inputs : List (CertifiedRelationalSymmetryInput molecule)) :
    validatedRelationalSymmetryDerivedMolecularFullereneConfigurationInputs molecule
        (inputs.map CertifiedRelationalSymmetryInput.sourceInput) =
      inputs.map fun input => input.sourceInput.cage := by
  induction inputs with
  | nil => rfl
  | cons input inputs ih =>
      unfold validatedRelationalSymmetryDerivedMolecularFullereneConfigurationInputs
      unfold validatedRelationalSymmetryDerivedMolecularFullereneConfigurationInputs at ih
      simp only [List.map_cons, List.filterMap_cons]
      have admittedEq :
          relationalSymmetryDerivedMolecularFullereneConfigurationInput? molecule
              input.sourceInput = some input.sourceInput.cage :=
        (relationalSymmetryDerivedMolecularFullereneConfigurationInput?_eq_some_iff
          molecule input.sourceInput input.sourceInput.cage).2 ⟨input.admitted, rfl⟩
      rw [admittedEq]
      simp only
      rw [ih]

private theorem validatedSymmetrySourceCages_eq_runtimeInputs
    (molecule : RawMolecule)
    (inputs : List (CertifiedRelationalSymmetryInput molecule)) :
    validatedMolecularFullereneConfigurationInputs molecule
        (inputs.map fun input => input.sourceInput.cage) =
      inputs.map fun input => input.runtimeInput.toFullereneConfigurationInput := by
  induction inputs with
  | nil => rfl
  | cons input inputs ih =>
      unfold validatedMolecularFullereneConfigurationInputs
      unfold validatedMolecularFullereneConfigurationInputs at ih
      simp only [List.map_cons, List.filterMap_cons]
      have admittedEq :
          molecularFullereneConfigurationInput? molecule input.sourceInput.cage =
            some input.sourceInput.cage.toFullereneConfigurationInput :=
        (molecularFullereneConfigurationInput?_eq_some_iff molecule input.sourceInput.cage
          input.sourceInput.cage.toFullereneConfigurationInput).2
          ⟨input.sourceCage_carrierJudged, rfl⟩
      rw [admittedEq]
      simp only
      rw [ih, ← input.runtimeInput_eq_sourceInput]

/-- Any finite certificate family proves that the fully computable frozen result is exactly the
independent symmetry-only relational result. -/
theorem analyzeFrozenRelationalSymmetryConfigurations_eq_independent
    (molecule : RawMolecule)
    (inputs : List (CertifiedRelationalSymmetryInput molecule)) :
    analyzeFrozenRelationalSymmetryConfigurations
        (inputs.map CertifiedRelationalSymmetryInput.runtimeInput) =
      analyzeRelationalSymmetryDerivedMolecularFullereneConfigurations molecule
        (inputs.map CertifiedRelationalSymmetryInput.sourceInput) := by
  rw [analyzeFrozenRelationalSymmetryConfigurations,
    analyzeRelationalSymmetryDerivedMolecularFullereneConfigurations,
    analyzeMolecularFullereneConfigurations,
    List.map_map,
    validatedRelationalSymmetrySources_eq_sourceCages,
    validatedSymmetrySourceCages_eq_runtimeInputs]
  rfl

/-- Direct membership bridge from frozen production output to the independent symmetry-only
assignment judgment. -/
theorem mem_analyzeFrozenRelationalSymmetryConfigurations_iff_independent
    (molecule : RawMolecule)
    (inputs : List (CertifiedRelationalSymmetryInput molecule))
    (assignment : FullereneConfigurationAssignment) :
    assignment ∈ analyzeFrozenRelationalSymmetryConfigurations
        (inputs.map CertifiedRelationalSymmetryInput.runtimeInput) ↔
      RelationalSymmetryDerivedMolecularFullereneConfigurationAssignmentJudgment molecule
        (inputs.map CertifiedRelationalSymmetryInput.sourceInput) assignment := by
  rw [analyzeFrozenRelationalSymmetryConfigurations_eq_independent,
    mem_analyzeRelationalSymmetryDerivedMolecularFullereneConfigurations_iff]

end BlueBookP93.Cyclic
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.CertifiedRelationalSymmetryInput.runtimeInput_eq_sourceInput
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.mem_analyzeRelationalSymmetryDerivedMolecularFullereneConfigurations_iff
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.mem_analyzeFrozenRelationalSymmetryConfigurations_iff
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.analyzeFrozenRelationalSymmetryConfigurations_eq_independent
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.mem_analyzeFrozenRelationalSymmetryConfigurations_iff_independent
