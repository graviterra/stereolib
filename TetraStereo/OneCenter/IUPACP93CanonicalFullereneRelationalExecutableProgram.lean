import TetraStereo.OneCenter.IUPACP93CanonicalFullereneRelationalExecutableInputs
import TetraStereo.OneCenter.IUPACP93CanonicalFullereneRelationalType4ExecutableInput
import TetraStereo.OneCenter.IUPACP93RelationalFullereneSourceAuditSchema

set_option autoImplicit false

/-!
# Complete indexed executable relational fullerene program

The production interface is a total function on the exact five-constructor release-row index.
The ordered table is derived from the exhaustive `ReleaseRow.all` enumeration, so row identity and
coverage do not depend on positional convention.  Every result remains connected both to its
canonical assignment and to the appropriate independent relational analyzer.
-/

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

/-- Total computable lookup for the executable analyzer output of every release row. -/
def iupacP93CanonicalFullereneExecutableAnalyzerResult :
    P93RelationalFullereneReleaseRow → List FullereneConfigurationAssignment
  | .inherentParent => iupacP93CanonicalFullereneC76Type1ExecutableAnalyzerResult
  | .inherentSubstitution => iupacP93CanonicalFullereneC60Type2ExecutableAnalyzerResult
  | .noninherentSubstitution => iupacP93CanonicalFullereneC60Type3ExecutableAnalyzerResult
  | .chiralSubstituents => iupacP93CanonicalFullereneC70Type4ExecutableAnalyzerResult
  | .superimposed => iupacP93CanonicalFullereneC70SuperimposedExecutableAnalyzerResult

/-- The canonical assignment indexed by the same release-row identity. -/
noncomputable def iupacP93CanonicalFullereneReleaseAssignment :
    P93RelationalFullereneReleaseRow → FullereneConfigurationAssignment
  | .inherentParent => iupacP93CanonicalFullereneC76Type1LocalAssignment
  | .inherentSubstitution => iupacP93CanonicalFullereneC60Type2LocalAssignment
  | .noninherentSubstitution => iupacP93CanonicalFullereneC60Type3LocalAssignment
  | .chiralSubstituents => iupacP93CanonicalFullereneC70Type4LocalAssignment
  | .superimposed => iupacP93CanonicalFullereneC70SuperimposedLocalAssignment

/-- Total independent-specification lookup.  Four rows use source orientation; Type 4 uses only
relational symmetry, exactly reflecting the evidence available for that printed row. -/
noncomputable def iupacP93CanonicalFullereneIndependentAnalyzerResult :
    P93RelationalFullereneReleaseRow → List FullereneConfigurationAssignment
  | .inherentParent =>
      analyzeRelationalSourceOrientedMolecularFullereneConfigurations
        iupacP93CanonicalFullereneC76Type1Molecule none
        [iupacP93CanonicalFullereneC76Type1RelationalSourceInput]
  | .inherentSubstitution =>
      analyzeRelationalSourceOrientedMolecularFullereneConfigurations
        iupacP93CanonicalFullereneC60Type2Molecule none
        [iupacP93CanonicalFullereneC60Type2RelationalSourceInput]
  | .noninherentSubstitution =>
      analyzeRelationalSourceOrientedMolecularFullereneConfigurations
        iupacP93CanonicalFullereneC60Type3Molecule none
        [iupacP93CanonicalFullereneC60Type3RelationalSourceInput]
  | .chiralSubstituents =>
      analyzeRelationalSymmetryDerivedMolecularFullereneConfigurations
        iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
        [iupacP93CanonicalFullereneC70Type4RelationalInput]
  | .superimposed =>
      analyzeRelationalSourceOrientedMolecularFullereneConfigurations
        iupacP93CanonicalFullereneC70SuperimposedMolecule none
        [iupacP93CanonicalFullereneC70SuperimposedRelationalSourceInput]

/-- Every indexed executable call emits exactly its canonical assignment. -/
@[simp] theorem iupacP93CanonicalFullereneExecutableAnalyzerResult_exact
    (row : P93RelationalFullereneReleaseRow) :
    iupacP93CanonicalFullereneExecutableAnalyzerResult row =
      [iupacP93CanonicalFullereneReleaseAssignment row] := by
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

/-- Every indexed executable call is extensionally equal to its independent relational analyzer. -/
theorem iupacP93CanonicalFullereneExecutableAnalyzerResult_eq_independent
    (row : P93RelationalFullereneReleaseRow) :
    iupacP93CanonicalFullereneExecutableAnalyzerResult row =
      iupacP93CanonicalFullereneIndependentAnalyzerResult row := by
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

/-- Ordered presentation table derived from the exhaustive release-row enumeration. -/
def iupacP93CanonicalFullereneExecutableReleaseTable :
    List (P93RelationalFullereneReleaseRow × List FullereneConfigurationAssignment) :=
  P93RelationalFullereneReleaseRow.all.map fun row =>
    (row, iupacP93CanonicalFullereneExecutableAnalyzerResult row)

/-- The table's row tags are exactly the exhaustive release-row enumeration. -/
@[simp] theorem iupacP93CanonicalFullereneExecutableReleaseTable_rows_exact :
    iupacP93CanonicalFullereneExecutableReleaseTable.map Prod.fst =
      P93RelationalFullereneReleaseRow.all := by
  rw [iupacP93CanonicalFullereneExecutableReleaseTable, List.map_map]
  change P93RelationalFullereneReleaseRow.all = P93RelationalFullereneReleaseRow.all
  rfl

/-- The indexed release table contains exactly five entries. -/
@[simp] theorem iupacP93CanonicalFullereneExecutableReleaseTable_length :
    iupacP93CanonicalFullereneExecutableReleaseTable.length = 5 := by
  simp [iupacP93CanonicalFullereneExecutableReleaseTable]

/-- No release-row tag occurs twice in the ordered executable table. -/
theorem iupacP93CanonicalFullereneExecutableReleaseTable_rows_nodup :
    (iupacP93CanonicalFullereneExecutableReleaseTable.map Prod.fst).Nodup := by
  rw [iupacP93CanonicalFullereneExecutableReleaseTable_rows_exact]
  exact P93RelationalFullereneReleaseRow.all_nodup

/-- Every release-row index occurs in the executable table with its total-lookup value. -/
theorem iupacP93CanonicalFullereneExecutableReleaseTable_contains
    (row : P93RelationalFullereneReleaseRow) :
    (row, iupacP93CanonicalFullereneExecutableAnalyzerResult row) ∈
      iupacP93CanonicalFullereneExecutableReleaseTable := by
  exact List.mem_map_of_mem (P93RelationalFullereneReleaseRow.mem_all row)

/-- Projecting the ordered table's results yields exactly one canonical assignment per row. -/
theorem iupacP93CanonicalFullereneExecutableReleaseTable_results_exact :
    iupacP93CanonicalFullereneExecutableReleaseTable.map Prod.snd =
      P93RelationalFullereneReleaseRow.all.map fun row =>
        [iupacP93CanonicalFullereneReleaseAssignment row] := by
  simp [iupacP93CanonicalFullereneExecutableReleaseTable]

/-- Each table entry is independently justified at its own release-row index. -/
theorem iupacP93CanonicalFullereneExecutableReleaseTable_all_independent :
    ∀ entry ∈ iupacP93CanonicalFullereneExecutableReleaseTable,
      entry.2 = iupacP93CanonicalFullereneIndependentAnalyzerResult entry.1 := by
  intro entry hentry
  simp only [iupacP93CanonicalFullereneExecutableReleaseTable, List.mem_map] at hentry
  obtain ⟨row, _, rfl⟩ := hentry
  exact iupacP93CanonicalFullereneExecutableAnalyzerResult_eq_independent row

end P93CanonicalProgramFullerene
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneExecutableAnalyzerResult_exact
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneExecutableAnalyzerResult_eq_independent
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneExecutableReleaseTable_rows_exact
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneExecutableReleaseTable_all_independent
