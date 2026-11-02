import TetraStereo.OneCenter.P93MolecularFullereneCertifiedRelationalProgram
import TetraStereo.OneCenter.IUPACP93CanonicalFullereneRelationalSourceInputs

set_option autoImplicit false

/-!
# Frozen executable inputs for the source-oriented canonical fullerene rows

Four printed rows have genuine source-oriented relational inputs.  Their proof-carrying source
records depend on proposition-valued symmetry constructions and therefore are intentionally
noncomputable.  This module keeps those records as specification bridges and separately freezes
the small runtime payloads consumed by `analyzeFullereneConfigurations`.  The runtime definitions
below contain only ranges, Boolean tests, descriptor data, and the existing finite analyzer.

The Type 4 row is deliberately absent: its source has no cage-numbering or turn payload, so it
cannot inhabit `RelationalSourceOrientedMolecularFullereneConfigurationInput`.  Its truthful
executable extension is a parallel symmetry-only certificate carrying the already-proved
`RelationalSymmetryDerivedMolecularFullereneConfigurationInputJudgment`, frozen test/unit data,
and no fabricated orientation witness.
-/

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

/-! ## Exact ascending carrier enumerations -/

theorem iupacP93CanonicalFullereneC76Type1SortedCarrier_exact :
    iupacP93CanonicalFullereneC76Type1RelationalSourceInput.symmetryInput.topologyInput.carrier.sort
        (· ≤ ·) =
      List.range 76 := by
  change (List.range 76).toFinset.sort (· ≤ ·) = List.range 76
  rw [List.toFinset_range, Finset.sort_range]

theorem iupacP93CanonicalFullereneC60Type2SortedCarrier_exact :
    iupacP93CanonicalFullereneC60Type2RelationalSourceInput.symmetryInput.topologyInput.carrier.sort
        (· ≤ ·) =
      List.range 60 := by
  change (List.range 60).toFinset.sort (· ≤ ·) = List.range 60
  rw [List.toFinset_range, Finset.sort_range]

theorem iupacP93CanonicalFullereneC60Type3SortedCarrier_exact :
    iupacP93CanonicalFullereneC60Type3RelationalSourceInput.symmetryInput.topologyInput.carrier.sort
        (· ≤ ·) =
      List.range 60 := by
  change (List.range 60).toFinset.sort (· ≤ ·) = List.range 60
  rw [List.toFinset_range, Finset.sort_range]

theorem iupacP93CanonicalFullereneC70SuperimposedSortedCarrier_exact :
    iupacP93CanonicalFullereneC70SuperimposedRelationalSourceInput.symmetryInput.topologyInput.carrier.sort
        (· ≤ ·) =
      List.range 70 := by
  change (List.range 70).toFinset.sort (· ≤ ·) = List.range 70
  rw [List.toFinset_range, Finset.sort_range]

/-! ## Computable frozen runtime data -/

def iupacP93CanonicalFullereneC76Type1RuntimeTest : FullereneSubstitutionTest :=
  ⟨true, true, true, true, false⟩

def iupacP93CanonicalFullereneC60Type2RuntimeTest : FullereneSubstitutionTest :=
  ⟨false, true, true, true, false⟩

def iupacP93CanonicalFullereneC60Type3RuntimeTest : FullereneSubstitutionTest :=
  ⟨false, true, false, true, false⟩

def iupacP93CanonicalFullereneC70SuperimposedRuntimeTest : FullereneSubstitutionTest :=
  ⟨false, true, true, true, true⟩

def iupacP93CanonicalFullereneHandedRuntimeDescriptorEvidence :
    FullereneDescriptorEvidence :=
  { cageNumberingKind := some .systematic
    cageTurn := some .clockwise
    everyChiralSubstituentHasCIP := false }

def iupacP93CanonicalFullereneSuperimposedRuntimeDescriptorEvidence :
    FullereneDescriptorEvidence :=
  { cageNumberingKind := some .systematic
    cageTurn := some .clockwise
    everyChiralSubstituentHasCIP := true }

def iupacP93CanonicalFullereneC76Type1FrozenRuntimeInput : FullereneConfigurationInput :=
  { unit := List.range 76
    substitutionTest := iupacP93CanonicalFullereneC76Type1RuntimeTest
    descriptorEvidence := iupacP93CanonicalFullereneHandedRuntimeDescriptorEvidence }

def iupacP93CanonicalFullereneC60Type2FrozenRuntimeInput : FullereneConfigurationInput :=
  { unit := List.range 60
    substitutionTest := iupacP93CanonicalFullereneC60Type2RuntimeTest
    descriptorEvidence := iupacP93CanonicalFullereneHandedRuntimeDescriptorEvidence }

def iupacP93CanonicalFullereneC60Type3FrozenRuntimeInput : FullereneConfigurationInput :=
  { unit := List.range 60
    substitutionTest := iupacP93CanonicalFullereneC60Type3RuntimeTest
    descriptorEvidence := iupacP93CanonicalFullereneHandedRuntimeDescriptorEvidence }

def iupacP93CanonicalFullereneC70SuperimposedFrozenRuntimeInput :
    FullereneConfigurationInput :=
  { unit := List.range 70
    substitutionTest := iupacP93CanonicalFullereneC70SuperimposedRuntimeTest
    descriptorEvidence := iupacP93CanonicalFullereneSuperimposedRuntimeDescriptorEvidence }

/-! ## Noncomputable proof-carrying specification bridges -/

noncomputable def iupacP93CanonicalFullereneC76Type1CertifiedRelationalInput :
    CertifiedRelationalSourceOrientedInput
      iupacP93CanonicalFullereneC76Type1Molecule none where
  sourceInput := iupacP93CanonicalFullereneC76Type1RelationalSourceInput
  frozenUnit := List.range 76
  frozenTest := iupacP93CanonicalFullereneC76Type1RuntimeTest
  admitted := iupacP93CanonicalFullereneC76Type1RelationalSourceInput_judged
  testExact := by
    simpa [iupacP93CanonicalFullereneC76Type1RuntimeTest,
      iupacP93CanonicalFullereneC76Type1ExpectedTest] using
      iupacP93CanonicalFullereneC76Type1RelationalTest_exact
  unitExact := iupacP93CanonicalFullereneC76Type1SortedCarrier_exact

noncomputable def iupacP93CanonicalFullereneC60Type2CertifiedRelationalInput :
    CertifiedRelationalSourceOrientedInput
      iupacP93CanonicalFullereneC60Type2Molecule none where
  sourceInput := iupacP93CanonicalFullereneC60Type2RelationalSourceInput
  frozenUnit := List.range 60
  frozenTest := iupacP93CanonicalFullereneC60Type2RuntimeTest
  admitted := iupacP93CanonicalFullereneC60Type2RelationalSourceInput_judged
  testExact := by
    simpa [iupacP93CanonicalFullereneC60Type2RuntimeTest,
      iupacP93CanonicalFullereneC60Type2ExpectedTest] using
      iupacP93CanonicalFullereneC60Type2RelationalTest_exact
  unitExact := iupacP93CanonicalFullereneC60Type2SortedCarrier_exact

noncomputable def iupacP93CanonicalFullereneC60Type3CertifiedRelationalInput :
    CertifiedRelationalSourceOrientedInput
      iupacP93CanonicalFullereneC60Type3Molecule none where
  sourceInput := iupacP93CanonicalFullereneC60Type3RelationalSourceInput
  frozenUnit := List.range 60
  frozenTest := iupacP93CanonicalFullereneC60Type3RuntimeTest
  admitted := iupacP93CanonicalFullereneC60Type3RelationalSourceInput_judged
  testExact := by
    simpa [iupacP93CanonicalFullereneC60Type3RuntimeTest,
      iupacP93CanonicalFullereneC60Type3ExpectedTest] using
      iupacP93CanonicalFullereneC60Type3RelationalTest_exact
  unitExact := iupacP93CanonicalFullereneC60Type3SortedCarrier_exact

noncomputable def iupacP93CanonicalFullereneC70SuperimposedCertifiedRelationalInput :
    CertifiedRelationalSourceOrientedInput
      iupacP93CanonicalFullereneC70SuperimposedMolecule none where
  sourceInput := iupacP93CanonicalFullereneC70SuperimposedRelationalSourceInput
  frozenUnit := List.range 70
  frozenTest := iupacP93CanonicalFullereneC70SuperimposedRuntimeTest
  admitted := iupacP93CanonicalFullereneC70SuperimposedRelationalSourceInput_judged
  testExact := by
    simpa [iupacP93CanonicalFullereneC70SuperimposedRuntimeTest,
      iupacP93CanonicalFullereneC70SuperimposedExpectedTest] using
      iupacP93CanonicalFullereneC70SuperimposedRelationalTest_exact
  unitExact := iupacP93CanonicalFullereneC70SuperimposedSortedCarrier_exact

/-! ## Fully executable singleton analyzers -/

def iupacP93CanonicalFullereneC76Type1ExecutableAnalyzerResult :
    List FullereneConfigurationAssignment :=
  analyzeFullereneConfigurations [iupacP93CanonicalFullereneC76Type1FrozenRuntimeInput]

def iupacP93CanonicalFullereneC60Type2ExecutableAnalyzerResult :
    List FullereneConfigurationAssignment :=
  analyzeFullereneConfigurations [iupacP93CanonicalFullereneC60Type2FrozenRuntimeInput]

def iupacP93CanonicalFullereneC60Type3ExecutableAnalyzerResult :
    List FullereneConfigurationAssignment :=
  analyzeFullereneConfigurations [iupacP93CanonicalFullereneC60Type3FrozenRuntimeInput]

def iupacP93CanonicalFullereneC70SuperimposedExecutableAnalyzerResult :
    List FullereneConfigurationAssignment :=
  analyzeFullereneConfigurations
    [iupacP93CanonicalFullereneC70SuperimposedFrozenRuntimeInput]

/-! ## Exact bridge back to the certified and independent analyzers -/

theorem iupacP93CanonicalFullereneC76Type1FrozenRuntimeInput_eq_certified :
    iupacP93CanonicalFullereneC76Type1FrozenRuntimeInput =
      iupacP93CanonicalFullereneC76Type1CertifiedRelationalInput.executableInput := by
  rfl

theorem iupacP93CanonicalFullereneC60Type2FrozenRuntimeInput_eq_certified :
    iupacP93CanonicalFullereneC60Type2FrozenRuntimeInput =
      iupacP93CanonicalFullereneC60Type2CertifiedRelationalInput.executableInput := by
  rfl

theorem iupacP93CanonicalFullereneC60Type3FrozenRuntimeInput_eq_certified :
    iupacP93CanonicalFullereneC60Type3FrozenRuntimeInput =
      iupacP93CanonicalFullereneC60Type3CertifiedRelationalInput.executableInput := by
  rfl

theorem iupacP93CanonicalFullereneC70SuperimposedFrozenRuntimeInput_eq_certified :
    iupacP93CanonicalFullereneC70SuperimposedFrozenRuntimeInput =
      iupacP93CanonicalFullereneC70SuperimposedCertifiedRelationalInput.executableInput := by
  rfl

theorem iupacP93CanonicalFullereneC76Type1ExecutableAnalyzer_eq_certified :
    iupacP93CanonicalFullereneC76Type1ExecutableAnalyzerResult =
      analyzeCertifiedRelationalSourceOrientedConfigurations
        iupacP93CanonicalFullereneC76Type1Molecule none
        [iupacP93CanonicalFullereneC76Type1CertifiedRelationalInput] := by
  rw [analyzeCertifiedRelationalSourceOrientedConfigurations, List.map_singleton,
    ← iupacP93CanonicalFullereneC76Type1FrozenRuntimeInput_eq_certified]
  rfl

theorem iupacP93CanonicalFullereneC60Type2ExecutableAnalyzer_eq_certified :
    iupacP93CanonicalFullereneC60Type2ExecutableAnalyzerResult =
      analyzeCertifiedRelationalSourceOrientedConfigurations
        iupacP93CanonicalFullereneC60Type2Molecule none
        [iupacP93CanonicalFullereneC60Type2CertifiedRelationalInput] := by
  rw [analyzeCertifiedRelationalSourceOrientedConfigurations, List.map_singleton,
    ← iupacP93CanonicalFullereneC60Type2FrozenRuntimeInput_eq_certified]
  rfl

theorem iupacP93CanonicalFullereneC60Type3ExecutableAnalyzer_eq_certified :
    iupacP93CanonicalFullereneC60Type3ExecutableAnalyzerResult =
      analyzeCertifiedRelationalSourceOrientedConfigurations
        iupacP93CanonicalFullereneC60Type3Molecule none
        [iupacP93CanonicalFullereneC60Type3CertifiedRelationalInput] := by
  rw [analyzeCertifiedRelationalSourceOrientedConfigurations, List.map_singleton,
    ← iupacP93CanonicalFullereneC60Type3FrozenRuntimeInput_eq_certified]
  rfl

theorem iupacP93CanonicalFullereneC70SuperimposedExecutableAnalyzer_eq_certified :
    iupacP93CanonicalFullereneC70SuperimposedExecutableAnalyzerResult =
      analyzeCertifiedRelationalSourceOrientedConfigurations
        iupacP93CanonicalFullereneC70SuperimposedMolecule none
        [iupacP93CanonicalFullereneC70SuperimposedCertifiedRelationalInput] := by
  rw [analyzeCertifiedRelationalSourceOrientedConfigurations, List.map_singleton,
    ← iupacP93CanonicalFullereneC70SuperimposedFrozenRuntimeInput_eq_certified]
  rfl

theorem iupacP93CanonicalFullereneC76Type1ExecutableAnalyzer_eq_independent :
    iupacP93CanonicalFullereneC76Type1ExecutableAnalyzerResult =
      analyzeRelationalSourceOrientedMolecularFullereneConfigurations
        iupacP93CanonicalFullereneC76Type1Molecule none
        [iupacP93CanonicalFullereneC76Type1RelationalSourceInput] := by
  rw [iupacP93CanonicalFullereneC76Type1ExecutableAnalyzer_eq_certified,
    analyzeCertifiedRelationalSourceOrientedConfigurations_eq_relational]
  rfl

theorem iupacP93CanonicalFullereneC60Type2ExecutableAnalyzer_eq_independent :
    iupacP93CanonicalFullereneC60Type2ExecutableAnalyzerResult =
      analyzeRelationalSourceOrientedMolecularFullereneConfigurations
        iupacP93CanonicalFullereneC60Type2Molecule none
        [iupacP93CanonicalFullereneC60Type2RelationalSourceInput] := by
  rw [iupacP93CanonicalFullereneC60Type2ExecutableAnalyzer_eq_certified,
    analyzeCertifiedRelationalSourceOrientedConfigurations_eq_relational]
  rfl

theorem iupacP93CanonicalFullereneC60Type3ExecutableAnalyzer_eq_independent :
    iupacP93CanonicalFullereneC60Type3ExecutableAnalyzerResult =
      analyzeRelationalSourceOrientedMolecularFullereneConfigurations
        iupacP93CanonicalFullereneC60Type3Molecule none
        [iupacP93CanonicalFullereneC60Type3RelationalSourceInput] := by
  rw [iupacP93CanonicalFullereneC60Type3ExecutableAnalyzer_eq_certified,
    analyzeCertifiedRelationalSourceOrientedConfigurations_eq_relational]
  rfl

theorem iupacP93CanonicalFullereneC70SuperimposedExecutableAnalyzer_eq_independent :
    iupacP93CanonicalFullereneC70SuperimposedExecutableAnalyzerResult =
      analyzeRelationalSourceOrientedMolecularFullereneConfigurations
        iupacP93CanonicalFullereneC70SuperimposedMolecule none
        [iupacP93CanonicalFullereneC70SuperimposedRelationalSourceInput] := by
  rw [iupacP93CanonicalFullereneC70SuperimposedExecutableAnalyzer_eq_certified,
    analyzeCertifiedRelationalSourceOrientedConfigurations_eq_relational]
  rfl

/-! ## Exact executable emissions -/

def iupacP93CanonicalFullereneC76Type1RuntimeAssignment :
    FullereneConfigurationAssignment :=
  { unit := List.range 76
    chiralityType := .inherentlyChiralParent
    payloads := [.cageHandedness .systematic .C] }

def iupacP93CanonicalFullereneC60Type2RuntimeAssignment :
    FullereneConfigurationAssignment :=
  { unit := List.range 60
    chiralityType := .inherentlyChiralSubstitutionPattern
    payloads := [.cageHandedness .systematic .C] }

def iupacP93CanonicalFullereneC60Type3RuntimeAssignment :
    FullereneConfigurationAssignment :=
  { unit := List.range 60
    chiralityType := .noninherentlyChiralSubstitutionPattern
    payloads := [.cageHandedness .systematic .C] }

def iupacP93CanonicalFullereneC70SuperimposedRuntimeAssignment :
    FullereneConfigurationAssignment :=
  { unit := List.range 70
    chiralityType := .inherentlyChiralSubstitutionPattern
    payloads := [.cageHandedness .systematic .C] }

theorem iupacP93CanonicalFullereneC76Type1ExecutableAnalyzer_exact :
    iupacP93CanonicalFullereneC76Type1ExecutableAnalyzerResult =
      [iupacP93CanonicalFullereneC76Type1RuntimeAssignment] := by
  decide

theorem iupacP93CanonicalFullereneC60Type2ExecutableAnalyzer_exact :
    iupacP93CanonicalFullereneC60Type2ExecutableAnalyzerResult =
      [iupacP93CanonicalFullereneC60Type2RuntimeAssignment] := by
  decide

theorem iupacP93CanonicalFullereneC60Type3ExecutableAnalyzer_exact :
    iupacP93CanonicalFullereneC60Type3ExecutableAnalyzerResult =
      [iupacP93CanonicalFullereneC60Type3RuntimeAssignment] := by
  decide

theorem iupacP93CanonicalFullereneC70SuperimposedExecutableAnalyzer_exact :
    iupacP93CanonicalFullereneC70SuperimposedExecutableAnalyzerResult =
      [iupacP93CanonicalFullereneC70SuperimposedRuntimeAssignment] := by
  decide

theorem iupacP93CanonicalFullereneC76Type1RuntimeAssignment_eq_canonical :
    iupacP93CanonicalFullereneC76Type1RuntimeAssignment =
      iupacP93CanonicalFullereneC76Type1LocalAssignment := by
  unfold iupacP93CanonicalFullereneC76Type1RuntimeAssignment
    iupacP93CanonicalFullereneC76Type1LocalAssignment
  have unitExact :
      iupacP93CanonicalFullereneC76Type1RelationalInput.cage.carrier.sort (· ≤ ·) =
        List.range 76 := by
    simpa [iupacP93CanonicalFullereneC76Type1RelationalSourceInput] using
      iupacP93CanonicalFullereneC76Type1SortedCarrier_exact
  rw [unitExact]

theorem iupacP93CanonicalFullereneC60Type2RuntimeAssignment_eq_canonical :
    iupacP93CanonicalFullereneC60Type2RuntimeAssignment =
      iupacP93CanonicalFullereneC60Type2LocalAssignment := by
  unfold iupacP93CanonicalFullereneC60Type2RuntimeAssignment
    iupacP93CanonicalFullereneC60Type2LocalAssignment
  have unitExact :
      iupacP93CanonicalFullereneC60Type2RelationalInput.cage.carrier.sort (· ≤ ·) =
        List.range 60 := by
    simpa [iupacP93CanonicalFullereneC60Type2RelationalSourceInput] using
      iupacP93CanonicalFullereneC60Type2SortedCarrier_exact
  rw [unitExact]

theorem iupacP93CanonicalFullereneC60Type3RuntimeAssignment_eq_canonical :
    iupacP93CanonicalFullereneC60Type3RuntimeAssignment =
      iupacP93CanonicalFullereneC60Type3LocalAssignment := by
  unfold iupacP93CanonicalFullereneC60Type3RuntimeAssignment
    iupacP93CanonicalFullereneC60Type3LocalAssignment
  have unitExact :
      iupacP93CanonicalFullereneC60Type3RelationalInput.cage.carrier.sort (· ≤ ·) =
        List.range 60 := by
    simpa [iupacP93CanonicalFullereneC60Type3RelationalSourceInput] using
      iupacP93CanonicalFullereneC60Type3SortedCarrier_exact
  rw [unitExact]

theorem iupacP93CanonicalFullereneC70SuperimposedRuntimeAssignment_eq_canonical :
    iupacP93CanonicalFullereneC70SuperimposedRuntimeAssignment =
      iupacP93CanonicalFullereneC70SuperimposedLocalAssignment := by
  unfold iupacP93CanonicalFullereneC70SuperimposedRuntimeAssignment
    iupacP93CanonicalFullereneC70SuperimposedLocalAssignment
  have unitExact :
      iupacP93CanonicalFullereneC70SuperimposedRelationalInput.cage.carrier.sort (· ≤ ·) =
        List.range 70 := by
    simpa [iupacP93CanonicalFullereneC70SuperimposedRelationalSourceInput] using
      iupacP93CanonicalFullereneC70SuperimposedSortedCarrier_exact
  rw [unitExact]

theorem iupacP93CanonicalFullereneExecutableAnalyzers_all_emit_canonical :
    iupacP93CanonicalFullereneC76Type1ExecutableAnalyzerResult =
        [iupacP93CanonicalFullereneC76Type1LocalAssignment] ∧
    iupacP93CanonicalFullereneC60Type2ExecutableAnalyzerResult =
        [iupacP93CanonicalFullereneC60Type2LocalAssignment] ∧
    iupacP93CanonicalFullereneC60Type3ExecutableAnalyzerResult =
        [iupacP93CanonicalFullereneC60Type3LocalAssignment] ∧
    iupacP93CanonicalFullereneC70SuperimposedExecutableAnalyzerResult =
        [iupacP93CanonicalFullereneC70SuperimposedLocalAssignment] := by
  exact ⟨iupacP93CanonicalFullereneC76Type1ExecutableAnalyzer_exact.trans
      (congrArg List.singleton
        iupacP93CanonicalFullereneC76Type1RuntimeAssignment_eq_canonical),
    iupacP93CanonicalFullereneC60Type2ExecutableAnalyzer_exact.trans
      (congrArg List.singleton
        iupacP93CanonicalFullereneC60Type2RuntimeAssignment_eq_canonical),
    iupacP93CanonicalFullereneC60Type3ExecutableAnalyzer_exact.trans
      (congrArg List.singleton
        iupacP93CanonicalFullereneC60Type3RuntimeAssignment_eq_canonical),
    iupacP93CanonicalFullereneC70SuperimposedExecutableAnalyzer_exact.trans
      (congrArg List.singleton
        iupacP93CanonicalFullereneC70SuperimposedRuntimeAssignment_eq_canonical)⟩

end P93CanonicalProgramFullerene
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC76Type1ExecutableAnalyzer_eq_independent
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC60Type2ExecutableAnalyzer_eq_independent
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC60Type3ExecutableAnalyzer_eq_independent
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC70SuperimposedExecutableAnalyzer_eq_independent
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneExecutableAnalyzers_all_emit_canonical
