import TetraStereo.OneCenter.P93MolecularFullereneCertifiedRelationalSymmetryProgram
import TetraStereo.OneCenter.IUPACP93CanonicalFullereneRelationalSourceInputs

set_option autoImplicit false

/-!
# Frozen executable input for the canonical Type 4 fullerene row

The page-82 Type 4 derivative is relationally symmetry-derived but intentionally has no cage
numbering or exterior-turn source.  It therefore uses the symmetry-only certified program rather
than the four-row source-oriented program.  Runtime computation is isolated from the
noncomputable graph/symmetry certificate and is proved equal to that independent specification.
-/

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

theorem iupacP93CanonicalFullereneC70Type4SortedCarrier_exact :
    iupacP93CanonicalFullereneC70Type4RelationalInput.topologyInput.carrier.sort (· ≤ ·) =
      List.range 70 := by
  change (List.range 70).toFinset.sort (· ≤ ·) = List.range 70
  rw [List.toFinset_range, Finset.sort_range]

/-- Fully executable Type 4 payload: no numbering kind and no cage turn are present. -/
def iupacP93CanonicalFullereneC70Type4FrozenRuntimeInput :
    FrozenRelationalSymmetryRuntimeInput :=
  { carrier := List.range 70
    substitutionTest := ⟨false, true, false, false, true⟩
    descriptorEvidence :=
      { cageNumberingKind := none
        cageTurn := none
        everyChiralSubstituentHasCIP := true } }

/-- Proof-only bridge to the graph-backed Type 4 relational source. -/
noncomputable def iupacP93CanonicalFullereneC70Type4CertifiedRelationalSymmetryInput :
    CertifiedRelationalSymmetryInput
      iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble where
  sourceInput := iupacP93CanonicalFullereneC70Type4RelationalInput
  runtimeInput := iupacP93CanonicalFullereneC70Type4FrozenRuntimeInput
  admitted := iupacP93CanonicalFullereneC70Type4RelationalInput_judged
  carrierExact := iupacP93CanonicalFullereneC70Type4SortedCarrier_exact
  testExact := by
    simpa [iupacP93CanonicalFullereneC70Type4FrozenRuntimeInput,
      iupacP93CanonicalFullereneC70Type4ExpectedTest] using
      iupacP93CanonicalFullereneC70Type4RelationalTest_exact
  descriptorExact := rfl

/-- Runtime result: this definition depends only on the frozen finite payload above. -/
def iupacP93CanonicalFullereneC70Type4ExecutableAnalyzerResult :
    List FullereneConfigurationAssignment :=
  analyzeFrozenRelationalSymmetryConfigurations
    [iupacP93CanonicalFullereneC70Type4FrozenRuntimeInput]

/-- The proof-carrying spelling is specification-only because it retains the relational source. -/
noncomputable def iupacP93CanonicalFullereneC70Type4CertifiedAnalyzerResult :
    List FullereneConfigurationAssignment :=
  analyzeFrozenRelationalSymmetryConfigurations
    [iupacP93CanonicalFullereneC70Type4CertifiedRelationalSymmetryInput.runtimeInput]

theorem iupacP93CanonicalFullereneC70Type4ExecutableAnalyzer_eq_certified :
    iupacP93CanonicalFullereneC70Type4ExecutableAnalyzerResult =
      iupacP93CanonicalFullereneC70Type4CertifiedAnalyzerResult := by
  rfl

theorem iupacP93CanonicalFullereneC70Type4ExecutableAnalyzer_eq_independent :
    iupacP93CanonicalFullereneC70Type4ExecutableAnalyzerResult =
      analyzeRelationalSymmetryDerivedMolecularFullereneConfigurations
        iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
        [iupacP93CanonicalFullereneC70Type4RelationalInput] := by
  rw [iupacP93CanonicalFullereneC70Type4ExecutableAnalyzer_eq_certified]
  simpa [iupacP93CanonicalFullereneC70Type4CertifiedAnalyzerResult] using
    (analyzeFrozenRelationalSymmetryConfigurations_eq_independent
      iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
      [iupacP93CanonicalFullereneC70Type4CertifiedRelationalSymmetryInput])

def iupacP93CanonicalFullereneC70Type4RuntimeAssignment :
    FullereneConfigurationAssignment :=
  { unit := List.range 70
    chiralityType := .chiralSubstituentsOnly
    payloads := [.substituentCIPComplete] }

theorem iupacP93CanonicalFullereneC70Type4ExecutableAnalyzer_exact :
    iupacP93CanonicalFullereneC70Type4ExecutableAnalyzerResult =
      [iupacP93CanonicalFullereneC70Type4RuntimeAssignment] := by
  decide

theorem iupacP93CanonicalFullereneC70Type4RuntimeAssignment_eq_canonical :
    iupacP93CanonicalFullereneC70Type4RuntimeAssignment =
      iupacP93CanonicalFullereneC70Type4LocalAssignment := by
  unfold iupacP93CanonicalFullereneC70Type4RuntimeAssignment
    iupacP93CanonicalFullereneC70Type4LocalAssignment
  have unitExact :
      iupacP93CanonicalFullereneC70Type4RelationalInput.cage.carrier.sort (· ≤ ·) =
        List.range 70 := by
    simpa using iupacP93CanonicalFullereneC70Type4SortedCarrier_exact
  rw [unitExact]

/-- The executable symmetry-only Type 4 analyzer emits exactly the existing canonical result. -/
theorem iupacP93CanonicalFullereneC70Type4ExecutableAnalyzer_emits_canonical :
    iupacP93CanonicalFullereneC70Type4ExecutableAnalyzerResult =
      [iupacP93CanonicalFullereneC70Type4LocalAssignment] :=
  iupacP93CanonicalFullereneC70Type4ExecutableAnalyzer_exact.trans
    (congrArg List.singleton
      iupacP93CanonicalFullereneC70Type4RuntimeAssignment_eq_canonical)

end P93CanonicalProgramFullerene
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC70Type4ExecutableAnalyzer_eq_independent
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC70Type4ExecutableAnalyzer_exact
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC70Type4ExecutableAnalyzer_emits_canonical
