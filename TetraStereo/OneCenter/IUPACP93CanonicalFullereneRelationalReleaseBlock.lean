import TetraStereo.OneCenter.IUPACP93CanonicalFullereneRelationalAuthorityObservations
import TetraStereo.OneCenter.IUPACP93CanonicalFullereneRelationalExecutableProgram

set_option autoImplicit false
set_option maxRecDepth 4096















namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

noncomputable section

/-! ## One indexed interface for the heterogeneous observations -/

/-- A release-row-tagged authority observation.  The constructor records which of the three
chemically truthful observation forms is available for that row. -/
inductive P93CanonicalRelationalFullereneAuthorityObservation
    (policy : P93RelationalFullereneAuthorityPolicy) where
  | inherentParent (value : P93RelationalFullereneHandedAuthorityObservation policy)
  | inherentSubstitution (value : P93RelationalFullereneHandedAuthorityObservation policy)
  | noninherentSubstitution (value : P93RelationalFullereneHandedAuthorityObservation policy)
  | chiralSubstituents (value : P93RelationalFullereneType4AuthorityObservation policy)
  | superimposed (value : P93RelationalFullereneSuperimposedAuthorityObservation policy)

namespace P93CanonicalRelationalFullereneAuthorityObservation

/-- Recover the exact release-row identity from an observation. -/
def releaseRow {policy : P93RelationalFullereneAuthorityPolicy} :
    P93CanonicalRelationalFullereneAuthorityObservation policy →
      P93RelationalFullereneReleaseRow
  | .inherentParent _ => .inherentParent
  | .inherentSubstitution _ => .inherentSubstitution
  | .noninherentSubstitution _ => .noninherentSubstitution
  | .chiralSubstituents _ => .chiralSubstituents
  | .superimposed _ => .superimposed

/-- The local fullerene assignment carried by any observation form. -/
def assignment {policy : P93RelationalFullereneAuthorityPolicy} :
    P93CanonicalRelationalFullereneAuthorityObservation policy →
      FullereneConfigurationAssignment
  | .inherentParent value => value.base.assignment
  | .inherentSubstitution value => value.base.assignment
  | .noninherentSubstitution value => value.base.assignment
  | .chiralSubstituents value => value.assignment
  | .superimposed value => value.handed.base.assignment

/-- Validity dispatches to the source-aware proposition appropriate to the observation form. -/
def ValidFor {policy : P93RelationalFullereneAuthorityPolicy}
    (observation : P93CanonicalRelationalFullereneAuthorityObservation policy)
    (source : AuthoritativeChemicalInput) : Prop :=
  match observation with
  | .inherentParent value => value.ValidFor policy source
  | .inherentSubstitution value => value.ValidFor policy source
  | .noninherentSubstitution value => value.ValidFor policy source
  | .chiralSubstituents value => value.ValidFor policy source
  | .superimposed value => value.ValidFor policy source

/-- Independent analyzer obtained from the fields of the observation itself.  Type 4 deliberately
uses the symmetry-only analyzer; all other rows use their source-oriented input family. -/
def independentAnalyzerResult {policy : P93RelationalFullereneAuthorityPolicy} :
    P93CanonicalRelationalFullereneAuthorityObservation policy →
      List FullereneConfigurationAssignment
  | .inherentParent value =>
      analyzeRelationalSourceOrientedMolecularFullereneConfigurations
        value.base.molecule value.base.spatial? value.base.inputs
  | .inherentSubstitution value =>
      analyzeRelationalSourceOrientedMolecularFullereneConfigurations
        value.base.molecule value.base.spatial? value.base.inputs
  | .noninherentSubstitution value =>
      analyzeRelationalSourceOrientedMolecularFullereneConfigurations
        value.base.molecule value.base.spatial? value.base.inputs
  | .chiralSubstituents value =>
      analyzeRelationalSymmetryDerivedMolecularFullereneConfigurations
        value.molecule [value.input]
  | .superimposed value =>
      analyzeRelationalSourceOrientedMolecularFullereneConfigurations
        value.handed.base.molecule value.handed.base.spatial? value.handed.base.inputs

end P93CanonicalRelationalFullereneAuthorityObservation

/-- Total observation lookup for the concrete five-row release. -/
def iupacP93CanonicalFullereneRelationalAuthorityObservation :
    P93RelationalFullereneReleaseRow →
      P93CanonicalRelationalFullereneAuthorityObservation
        iupacP93CanonicalFullereneRelationalSourceAudit.policy
  | .inherentParent =>
      .inherentParent iupacP93CanonicalFullereneC76Type1AuthorityObservation
  | .inherentSubstitution =>
      .inherentSubstitution iupacP93CanonicalFullereneC60Type2AuthorityObservation
  | .noninherentSubstitution =>
      .noninherentSubstitution iupacP93CanonicalFullereneC60Type3AuthorityObservation
  | .chiralSubstituents =>
      .chiralSubstituents iupacP93CanonicalFullereneC70Type4AuthorityObservation
  | .superimposed =>
      .superimposed iupacP93CanonicalFullereneC70SuperimposedAuthorityObservation

@[simp] theorem iupacP93CanonicalFullereneRelationalAuthorityObservation_row_exact
    (row : P93RelationalFullereneReleaseRow) :
    (iupacP93CanonicalFullereneRelationalAuthorityObservation row).releaseRow = row := by
  cases row <;> rfl



theorem iupacP93CanonicalFullereneRelationalAuthorityObservation_valid
    (row : P93RelationalFullereneReleaseRow) :
    (iupacP93CanonicalFullereneRelationalAuthorityObservation row).ValidFor
      (iupacP93CanonicalFullereneRelationalSourceAudit.row row).source := by
  cases row with
  | inherentParent => exact iupacP93CanonicalFullereneC76Type1AuthorityObservation_valid
  | inherentSubstitution => exact iupacP93CanonicalFullereneC60Type2AuthorityObservation_valid
  | noninherentSubstitution => exact iupacP93CanonicalFullereneC60Type3AuthorityObservation_valid
  | chiralSubstituents => exact iupacP93CanonicalFullereneC70Type4AuthorityObservation_valid
  | superimposed => exact iupacP93CanonicalFullereneC70SuperimposedAuthorityObservation_valid

/-- The total executable program equals the independent analyzer obtained directly from the
corresponding observation. -/
theorem iupacP93CanonicalFullereneExecutableAnalyzerResult_eq_observationIndependent
    (row : P93RelationalFullereneReleaseRow) :
    iupacP93CanonicalFullereneExecutableAnalyzerResult row =
      (iupacP93CanonicalFullereneRelationalAuthorityObservation row).independentAnalyzerResult := by
  cases row with
  | inherentParent =>
      exact iupacP93CanonicalFullereneC76Type1ExecutableAnalyzer_eq_independent
  | inherentSubstitution =>
      exact iupacP93CanonicalFullereneC60Type2ExecutableAnalyzer_eq_independent
  | noninherentSubstitution =>
      exact iupacP93CanonicalFullereneC60Type3ExecutableAnalyzer_eq_independent
  | chiralSubstituents =>
      exact iupacP93CanonicalFullereneC70Type4ExecutableAnalyzer_eq_independent
  | superimposed =>
      exact iupacP93CanonicalFullereneC70SuperimposedExecutableAnalyzer_eq_independent

/-- The total executable program emits exactly the assignment carried by its observation. -/
theorem iupacP93CanonicalFullereneExecutableAnalyzerResult_eq_observationAssignment
    (row : P93RelationalFullereneReleaseRow) :
    iupacP93CanonicalFullereneExecutableAnalyzerResult row =
      [(iupacP93CanonicalFullereneRelationalAuthorityObservation row).assignment] := by
  cases row with
  | inherentParent =>
      exact iupacP93CanonicalFullereneExecutableAnalyzers_all_emit_canonical.1
  | inherentSubstitution =>
      exact iupacP93CanonicalFullereneExecutableAnalyzers_all_emit_canonical.2.1
  | noninherentSubstitution =>
      exact iupacP93CanonicalFullereneExecutableAnalyzers_all_emit_canonical.2.2.1
  | chiralSubstituents =>
      exact iupacP93CanonicalFullereneC70Type4ExecutableAnalyzer_emits_canonical
  | superimposed =>
      exact iupacP93CanonicalFullereneExecutableAnalyzers_all_emit_canonical.2.2.2

/-! ## Single downstream release certificate -/

/-- The proof-carrying release object.  Its functions are total on the release index, so no row can
be omitted or silently reordered. -/
structure P93CanonicalRelationalFullereneReleaseBlock where
  audit : P93RelationalFullereneSourceAudit
  observation : P93RelationalFullereneReleaseRow →
    P93CanonicalRelationalFullereneAuthorityObservation audit.policy
  executableOutput : P93RelationalFullereneReleaseRow →
    List FullereneConfigurationAssignment
  observationRowExact : ∀ row, (observation row).releaseRow = row
  observationValid : ∀ row, (observation row).ValidFor (audit.row row).source
  executableIndependent : ∀ row,
    executableOutput row = (observation row).independentAnalyzerResult
  executableObservationExact : ∀ row,
    executableOutput row = [(observation row).assignment]

/-- The complete canonical five-row release certificate. -/
def iupacP93CanonicalFullereneRelationalReleaseBlock :
    P93CanonicalRelationalFullereneReleaseBlock where
  audit := iupacP93CanonicalFullereneRelationalSourceAudit
  observation := iupacP93CanonicalFullereneRelationalAuthorityObservation
  executableOutput := iupacP93CanonicalFullereneExecutableAnalyzerResult
  observationRowExact :=
    iupacP93CanonicalFullereneRelationalAuthorityObservation_row_exact
  observationValid := iupacP93CanonicalFullereneRelationalAuthorityObservation_valid
  executableIndependent :=
    iupacP93CanonicalFullereneExecutableAnalyzerResult_eq_observationIndependent
  executableObservationExact :=
    iupacP93CanonicalFullereneExecutableAnalyzerResult_eq_observationAssignment


@[simp] theorem iupacP93CanonicalFullereneRelationalReleaseBlock_audit_exact :
    iupacP93CanonicalFullereneRelationalReleaseBlock.audit =
      iupacP93CanonicalFullereneRelationalSourceAudit := by
  rfl

/-- Exact row coverage: projecting the block's audited row identities gives the exhaustive index. -/
theorem iupacP93CanonicalFullereneRelationalReleaseBlock_rows_exact :
    iupacP93CanonicalFullereneRelationalReleaseBlock.audit.rows.map
        IUPACP93RelationalFullereneAuthorityAuditRow.releaseRow =
      P93RelationalFullereneReleaseRow.all := by
  exact iupacP93CanonicalFullereneRelationalReleaseBlock.audit.rows_releaseRows_exact

/-- Exact source coverage in the same exhaustive release-index order. -/
theorem iupacP93CanonicalFullereneRelationalReleaseBlock_sources_exact :
    iupacP93CanonicalFullereneRelationalReleaseBlock.audit.rows.map
        IUPACP93RelationalFullereneAuthorityAuditRow.source =
      [iupacP93CanonicalFullereneC76Type1AuthoritySource,
        iupacP93CanonicalFullereneC60Type2AuthoritySource,
        iupacP93CanonicalFullereneC60Type3AuthoritySource,
        iupacP93CanonicalFullereneC70Type4AuthoritySource,
        iupacP93CanonicalFullereneC70SuperimposedAuthoritySource] := by
  rfl

/-- The exact five source rows are duplicate-free. -/
theorem iupacP93CanonicalFullereneRelationalReleaseBlock_sources_nodup :
    (iupacP93CanonicalFullereneRelationalReleaseBlock.audit.rows.map
      IUPACP93RelationalFullereneAuthorityAuditRow.source).Nodup := by
  exact iupacP93CanonicalFullereneRelationalReleaseBlock.audit.rows_sources_nodup

/-- The block's ordered executable table is derived from the exhaustive release index. -/
def iupacP93CanonicalFullereneRelationalReleaseBlock_executableTable :
    List (P93RelationalFullereneReleaseRow × List FullereneConfigurationAssignment) :=
  P93RelationalFullereneReleaseRow.all.map fun row =>
    (row, iupacP93CanonicalFullereneRelationalReleaseBlock.executableOutput row)

@[simp] theorem iupacP93CanonicalFullereneRelationalReleaseBlock_executableTable_rows_exact :
    iupacP93CanonicalFullereneRelationalReleaseBlock_executableTable.map Prod.fst =
      P93RelationalFullereneReleaseRow.all := by
  rw [iupacP93CanonicalFullereneRelationalReleaseBlock_executableTable, List.map_map]
  change P93RelationalFullereneReleaseRow.all = P93RelationalFullereneReleaseRow.all
  rfl

/-- Every row in the single release object is source-valid and its executable result agrees with
both the independent observation analyzer and the observation's exact canonical assignment. -/
theorem iupacP93CanonicalFullereneRelationalReleaseBlock_complete
    (row : P93RelationalFullereneReleaseRow) :
    (iupacP93CanonicalFullereneRelationalReleaseBlock.observation row).ValidFor
        (iupacP93CanonicalFullereneRelationalReleaseBlock.audit.row row).source ∧
      iupacP93CanonicalFullereneRelationalReleaseBlock.executableOutput row =
        (iupacP93CanonicalFullereneRelationalReleaseBlock.observation row).independentAnalyzerResult ∧
      iupacP93CanonicalFullereneRelationalReleaseBlock.executableOutput row =
        [(iupacP93CanonicalFullereneRelationalReleaseBlock.observation row).assignment] :=
  ⟨iupacP93CanonicalFullereneRelationalReleaseBlock.observationValid row,
    iupacP93CanonicalFullereneRelationalReleaseBlock.executableIndependent row,
    iupacP93CanonicalFullereneRelationalReleaseBlock.executableObservationExact row⟩

end
end P93CanonicalProgramFullerene
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneRelationalAuthorityObservation_valid
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneExecutableAnalyzerResult_eq_observationIndependent
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneRelationalReleaseBlock_rows_exact
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneRelationalReleaseBlock_sources_exact
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneRelationalReleaseBlock_complete
