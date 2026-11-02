import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC60DerivativeSymmetryAudit
import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC70DerivativeSymmetryAudit
import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC70SuperimposedSymmetryAudit
import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC76SymmetryAudit
import TetraStereo.OneCenter.P93FullereneConfigurationCompleteness

set_option autoImplicit false

/-!
# Exact relational classification of all five printed fullerene derivatives

The graph compiler, parent-cage symmetry audits, whole-addend relational symmetry proofs,
chiral-addend partition, and explicitly retained whole-derivative chirality observation meet
here.  The result is the complete five-field P-93.5.6 substitution test for every printed
derivative, followed by the independent and executable four-way classification.  No row supplies
a classification Boolean.  The second field is deliberately not described as graph-derived:
whole-derivative chirality remains independent chemical evidence at this layer.
-/

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

noncomputable section

private theorem fullereneSubstitutionTest_ext
    {left right : FullereneSubstitutionTest}
    (parent : left.parentChiral = right.parentChiral)
    (original : left.originalDerivativeChiral = right.originalDerivativeChiral)
    (sameTest : left.allSubstituentsReplacedByAchiralTChiral =
      right.allSubstituentsReplacedByAchiralTChiral)
    (actual : left.substitutionPatternWithActualIdentitiesChiral =
      right.substitutionPatternWithActualIdentitiesChiral)
    (hasChiral : left.hasChiralSubstituent = right.hasChiralSubstituent) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Appending any audited addends leaves the parent-color chirality result unchanged. -/
theorem compiledDerivative_parentColoringChiral_iff
    {core : RawMolecule} {package : MolecularFullereneNumberedCagePackage}
    (assembly : MolecularFullereneAddendTemplateAssembly core package.carrier)
    (certificate : package.Certificate core) :
    MolecularFullereneColoringChiral core package.topologyInput
        molecularFullereneParentColor ↔
      MolecularFullereneColoringChiral assembly.compileExtension.assemble
        package.topologyInput molecularFullereneParentColor := by
  exact (assembly.compileExtension.cageAgreement certificate).coloringChiral_iff
    certificate.oriented (assembly.transportCertificate certificate).oriented
    molecularFullereneParentColor

def iupacP93CanonicalFullereneC76Type1ExpectedTest : FullereneSubstitutionTest :=
  ⟨true, true, true, true, false⟩

def iupacP93CanonicalFullereneC60Type2ExpectedTest : FullereneSubstitutionTest :=
  ⟨false, true, true, true, false⟩

def iupacP93CanonicalFullereneC60Type3ExpectedTest : FullereneSubstitutionTest :=
  ⟨false, true, false, true, false⟩

def iupacP93CanonicalFullereneC70Type4ExpectedTest : FullereneSubstitutionTest :=
  ⟨false, true, false, false, true⟩

def iupacP93CanonicalFullereneC70SuperimposedExpectedTest : FullereneSubstitutionTest :=
  ⟨false, true, true, true, true⟩

private theorem c76ChiralAddends_empty :
    iupacP93CanonicalFullereneC76Type1RelationalEvidence.chiralAddends = ∅ := by
  change iupacP93CanonicalFullereneC76Type1Assembly.compiledChiralAddends = ∅
  exact iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.1

private theorem c60Type2ChiralAddends_empty :
    iupacP93CanonicalFullereneC60Type2RelationalEvidence.chiralAddends = ∅ := by
  change iupacP93CanonicalFullereneC60Type2Assembly.compiledChiralAddends = ∅
  exact iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.2.1

private theorem c60Type3ChiralAddends_empty :
    iupacP93CanonicalFullereneC60Type3RelationalEvidence.chiralAddends = ∅ := by
  change iupacP93CanonicalFullereneC60Type3Assembly.compiledChiralAddends = ∅
  exact iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.2.2.1

private theorem noChiralAddend_of_empty
    {molecule : RawMolecule} {input : MolecularFullereneConfigurationInput}
    (evidence : MolecularFullereneAddendRelationalEvidence molecule input.carrier)
    (empty : evidence.chiralAddends = ∅) :
    (deriveMolecularFullereneRelationalSubstitutionTest molecule input
      evidence).hasChiralSubstituent = false := by
  apply Bool.eq_false_of_not_eq_true
  intro positive
  have nonempty :=
    (deriveMolecularFullereneRelationalSubstitutionTest_hasChiralAddend_iff
      molecule input evidence).1 positive
  rw [empty] at nonempty
  exact Finset.not_nonempty_empty nonempty

private theorem hasChiralAddend_of_all
    {molecule : RawMolecule} {input : MolecularFullereneConfigurationInput}
    (evidence : MolecularFullereneAddendRelationalEvidence molecule input.carrier)
    (allChiral : evidence.chiralAddends = evidence.addends.toFinset) :
    (deriveMolecularFullereneRelationalSubstitutionTest molecule input
      evidence).hasChiralSubstituent = true := by
  apply (deriveMolecularFullereneRelationalSubstitutionTest_hasChiralAddend_iff
    molecule input evidence).2
  cases addendsEq : evidence.addends with
  | nil => exact False.elim (evidence.addendsNonempty addendsEq)
  | cons addend rest =>
      refine ⟨addend, ?_⟩
      rw [allChiral]
      simp [addendsEq]

theorem iupacP93CanonicalFullereneC76Type1RelationalTest_exact :
    deriveMolecularFullereneRelationalSubstitutionTest
        iupacP93CanonicalFullereneC76Type1Molecule
        iupacP93CanonicalFullereneC76DerivativeTopologyInput
        iupacP93CanonicalFullereneC76Type1RelationalEvidence =
      iupacP93CanonicalFullereneC76Type1ExpectedTest := by
  apply fullereneSubstitutionTest_ext
  · exact (deriveMolecularFullereneRelationalSubstitutionTest_parentChiral_iff
      _ _ _).2 iupacP93CanonicalFullereneC76_parent_chiral
  · rfl
  · exact (deriveMolecularFullereneRelationalSubstitutionTest_sameTest_iff
      _ _ _).2 iupacP93CanonicalFullereneC76Type1_sameTest_chiral
  · exact (deriveMolecularFullereneRelationalSubstitutionTest_actualIdentities_iff
      _ _ _).2 iupacP93CanonicalFullereneC76Type1_actual_chiral
  · exact noChiralAddend_of_empty _ c76ChiralAddends_empty

private theorem c60Type2_parent_achiral :
    ¬MolecularFullereneColoringChiral
      iupacP93CanonicalFullereneC60Type2Molecule
      iupacP93CanonicalFullereneC60DerivativeTopologyInput
      molecularFullereneParentColor := by
  intro type2ParentChiral
  have coreParentChiral :=
    (compiledDerivative_parentColoringChiral_iff
      iupacP93CanonicalFullereneC60Type2Assembly
      iupacP93CanonicalFullereneC60Certificate).2 type2ParentChiral
  have type3ParentChiral :=
    (compiledDerivative_parentColoringChiral_iff
      iupacP93CanonicalFullereneC60Type3Assembly
      iupacP93CanonicalFullereneC60Certificate).1 coreParentChiral
  exact iupacP93CanonicalFullereneC60Type3_sameTest_achiral
    (molecularFullereneParentChiral_implies_relational type3ParentChiral
      (MolecularFullereneSameTestAddendPatternPreserved
        iupacP93CanonicalFullereneC60Type3RelationalEvidence))

theorem iupacP93CanonicalFullereneC60Type2RelationalTest_exact :
    deriveMolecularFullereneRelationalSubstitutionTest
        iupacP93CanonicalFullereneC60Type2Molecule
        iupacP93CanonicalFullereneC60DerivativeTopologyInput
        iupacP93CanonicalFullereneC60Type2RelationalEvidence =
      iupacP93CanonicalFullereneC60Type2ExpectedTest := by
  apply fullereneSubstitutionTest_ext
  · apply Bool.eq_false_of_not_eq_true
    intro positive
    exact c60Type2_parent_achiral
      ((deriveMolecularFullereneRelationalSubstitutionTest_parentChiral_iff _ _ _).1 positive)
  · rfl
  · exact (deriveMolecularFullereneRelationalSubstitutionTest_sameTest_iff
      _ _ _).2 iupacP93CanonicalFullereneC60Type2_sameTest_chiral
  · exact (deriveMolecularFullereneRelationalSubstitutionTest_actualIdentities_iff
      _ _ _).2 iupacP93CanonicalFullereneC60Type2_actual_chiral
  · exact noChiralAddend_of_empty _ c60Type2ChiralAddends_empty

private theorem c60Type3_parent_achiral :
    ¬MolecularFullereneColoringChiral
      iupacP93CanonicalFullereneC60Type3Molecule
      iupacP93CanonicalFullereneC60DerivativeTopologyInput
      molecularFullereneParentColor := by
  intro parentChiral
  exact iupacP93CanonicalFullereneC60Type3_sameTest_achiral
    (molecularFullereneParentChiral_implies_relational parentChiral
      (MolecularFullereneSameTestAddendPatternPreserved
        iupacP93CanonicalFullereneC60Type3RelationalEvidence))

theorem iupacP93CanonicalFullereneC60Type3RelationalTest_exact :
    deriveMolecularFullereneRelationalSubstitutionTest
        iupacP93CanonicalFullereneC60Type3Molecule
        iupacP93CanonicalFullereneC60DerivativeTopologyInput
        iupacP93CanonicalFullereneC60Type3RelationalEvidence =
      iupacP93CanonicalFullereneC60Type3ExpectedTest := by
  apply fullereneSubstitutionTest_ext
  · apply Bool.eq_false_of_not_eq_true
    intro positive
    exact c60Type3_parent_achiral
      ((deriveMolecularFullereneRelationalSubstitutionTest_parentChiral_iff _ _ _).1 positive)
  · rfl
  · apply Bool.eq_false_of_not_eq_true
    intro positive
    exact iupacP93CanonicalFullereneC60Type3_sameTest_achiral
      ((deriveMolecularFullereneRelationalSubstitutionTest_sameTest_iff _ _ _).1 positive)
  · exact (deriveMolecularFullereneRelationalSubstitutionTest_actualIdentities_iff
      _ _ _).2 iupacP93CanonicalFullereneC60Type3_actual_chiral
  · exact noChiralAddend_of_empty _ c60Type3ChiralAddends_empty

private theorem c70Type4_parent_achiral :
    ¬MolecularFullereneColoringChiral
      iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
      iupacP93CanonicalFullereneC70DerivativeInput
      molecularFullereneParentColor := by
  intro parentChiral
  exact iupacP93CanonicalFullereneC70Type4_sameTestPattern_achiral
    (molecularFullereneParentChiral_implies_relational parentChiral
      (MolecularFullereneSameTestAddendPatternPreserved
        iupacP93CanonicalFullereneC70Type4RelationalEvidence))

private theorem c70Type4ChiralAddends_all :
    iupacP93CanonicalFullereneC70Type4RelationalEvidence.chiralAddends =
      iupacP93CanonicalFullereneC70Type4RelationalEvidence.addends.toFinset := by
  change iupacP93CanonicalFullereneC70Type4Assembly.compiledChiralAddends =
    iupacP93CanonicalFullereneC70Type4Assembly.compiledAddends.toFinset
  exact iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.2.2.2.1

theorem iupacP93CanonicalFullereneC70Type4RelationalTest_exact :
    deriveMolecularFullereneRelationalSubstitutionTest
        iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
        iupacP93CanonicalFullereneC70DerivativeInput
        iupacP93CanonicalFullereneC70Type4RelationalEvidence =
      iupacP93CanonicalFullereneC70Type4ExpectedTest := by
  apply fullereneSubstitutionTest_ext
  · apply Bool.eq_false_of_not_eq_true
    intro positive
    exact c70Type4_parent_achiral
      ((deriveMolecularFullereneRelationalSubstitutionTest_parentChiral_iff _ _ _).1 positive)
  · rfl
  · apply Bool.eq_false_of_not_eq_true
    intro positive
    exact iupacP93CanonicalFullereneC70Type4_sameTestPattern_achiral
      ((deriveMolecularFullereneRelationalSubstitutionTest_sameTest_iff _ _ _).1 positive)
  · apply Bool.eq_false_of_not_eq_true
    intro positive
    exact iupacP93CanonicalFullereneC70Type4_actualPattern_achiral
      ((deriveMolecularFullereneRelationalSubstitutionTest_actualIdentities_iff _ _ _).1 positive)
  · exact hasChiralAddend_of_all _ c70Type4ChiralAddends_all

private theorem c70Superimposed_parent_achiral :
    ¬MolecularFullereneColoringChiral
      iupacP93CanonicalFullereneC70SuperimposedMolecule
      iupacP93CanonicalFullereneC70SuperimposedTopologyInput
      molecularFullereneParentColor := by
  intro superimposedParentChiral
  have coreParentChiral :=
    (compiledDerivative_parentColoringChiral_iff
      iupacP93CanonicalFullereneC70SuperimposedAssembly
      iupacP93CanonicalFullereneC70SharedNumberedCage.certificate).2
        superimposedParentChiral
  have type4ParentChiral :=
    (compiledDerivative_parentColoringChiral_iff
      iupacP93CanonicalFullereneC70Type4Assembly
      iupacP93CanonicalFullereneC70SharedNumberedCage.certificate).1 coreParentChiral
  exact c70Type4_parent_achiral type4ParentChiral

private theorem c70SuperimposedChiralAddends_all :
    iupacP93CanonicalFullereneC70SuperimposedRelationalEvidence.chiralAddends =
      iupacP93CanonicalFullereneC70SuperimposedRelationalEvidence.addends.toFinset := by
  change iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledChiralAddends =
    iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledAddends.toFinset
  exact iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.2.2.2.2

theorem iupacP93CanonicalFullereneC70SuperimposedRelationalTest_exact :
    deriveMolecularFullereneRelationalSubstitutionTest
        iupacP93CanonicalFullereneC70SuperimposedMolecule
        iupacP93CanonicalFullereneC70SuperimposedTopologyInput
        iupacP93CanonicalFullereneC70SuperimposedRelationalEvidence =
      iupacP93CanonicalFullereneC70SuperimposedExpectedTest := by
  apply fullereneSubstitutionTest_ext
  · apply Bool.eq_false_of_not_eq_true
    intro positive
    exact c70Superimposed_parent_achiral
      ((deriveMolecularFullereneRelationalSubstitutionTest_parentChiral_iff _ _ _).1 positive)
  · rfl
  · exact (deriveMolecularFullereneRelationalSubstitutionTest_sameTest_iff
      _ _ _).2 iupacP93CanonicalFullereneC70Superimposed_sameTest_chiral
  · exact (deriveMolecularFullereneRelationalSubstitutionTest_actualIdentities_iff
      _ _ _).2 iupacP93CanonicalFullereneC70Superimposed_actual_chiral
  · exact hasChiralAddend_of_all _ c70SuperimposedChiralAddends_all

/-- One theorem assembles all five fields for every row; the second field remains the explicit
whole-derivative chemical observation identified in the module header. -/
theorem iupacP93CanonicalFullereneRelationalTests_all_exact :
    deriveMolecularFullereneRelationalSubstitutionTest
        iupacP93CanonicalFullereneC76Type1Molecule
        iupacP93CanonicalFullereneC76DerivativeTopologyInput
        iupacP93CanonicalFullereneC76Type1RelationalEvidence =
          iupacP93CanonicalFullereneC76Type1ExpectedTest ∧
    deriveMolecularFullereneRelationalSubstitutionTest
        iupacP93CanonicalFullereneC60Type2Molecule
        iupacP93CanonicalFullereneC60DerivativeTopologyInput
        iupacP93CanonicalFullereneC60Type2RelationalEvidence =
          iupacP93CanonicalFullereneC60Type2ExpectedTest ∧
    deriveMolecularFullereneRelationalSubstitutionTest
        iupacP93CanonicalFullereneC60Type3Molecule
        iupacP93CanonicalFullereneC60DerivativeTopologyInput
        iupacP93CanonicalFullereneC60Type3RelationalEvidence =
          iupacP93CanonicalFullereneC60Type3ExpectedTest ∧
    deriveMolecularFullereneRelationalSubstitutionTest
        iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
        iupacP93CanonicalFullereneC70DerivativeInput
        iupacP93CanonicalFullereneC70Type4RelationalEvidence =
          iupacP93CanonicalFullereneC70Type4ExpectedTest ∧
    deriveMolecularFullereneRelationalSubstitutionTest
        iupacP93CanonicalFullereneC70SuperimposedMolecule
        iupacP93CanonicalFullereneC70SuperimposedTopologyInput
        iupacP93CanonicalFullereneC70SuperimposedRelationalEvidence =
          iupacP93CanonicalFullereneC70SuperimposedExpectedTest :=
  ⟨iupacP93CanonicalFullereneC76Type1RelationalTest_exact,
    iupacP93CanonicalFullereneC60Type2RelationalTest_exact,
    iupacP93CanonicalFullereneC60Type3RelationalTest_exact,
    iupacP93CanonicalFullereneC70Type4RelationalTest_exact,
    iupacP93CanonicalFullereneC70SuperimposedRelationalTest_exact⟩

theorem iupacP93CanonicalFullereneRelationalTypes_all_match :
    FullereneTypeMatches iupacP93CanonicalFullereneC76Type1ExpectedTest
        .inherentlyChiralParent ∧
    FullereneTypeMatches iupacP93CanonicalFullereneC60Type2ExpectedTest
        .inherentlyChiralSubstitutionPattern ∧
    FullereneTypeMatches iupacP93CanonicalFullereneC60Type3ExpectedTest
        .noninherentlyChiralSubstitutionPattern ∧
    FullereneTypeMatches iupacP93CanonicalFullereneC70Type4ExpectedTest
        .chiralSubstituentsOnly ∧
    FullereneTypeMatches iupacP93CanonicalFullereneC70SuperimposedExpectedTest
        .inherentlyChiralSubstitutionPattern := by
  simp [FullereneTypeMatches, iupacP93CanonicalFullereneC76Type1ExpectedTest,
    iupacP93CanonicalFullereneC60Type2ExpectedTest,
    iupacP93CanonicalFullereneC60Type3ExpectedTest,
    iupacP93CanonicalFullereneC70Type4ExpectedTest,
    iupacP93CanonicalFullereneC70SuperimposedExpectedTest]

/-- For the five frozen raw evidence records, the executable classifier returns the independently
defined class relation.  This is a computation theorem, not yet a source-authority theorem:
release-facing use must pass through a valid relational authority observation, which separately
authorizes whole-derivative chirality, the chiral-addend partition, and exterior sense. -/
theorem iupacP93CanonicalFullereneRelationalClassifier_all_exact :
    fullereneChiralityType? iupacP93CanonicalFullereneC76Type1ExpectedTest =
        some .inherentlyChiralParent ∧
    fullereneChiralityType? iupacP93CanonicalFullereneC60Type2ExpectedTest =
        some .inherentlyChiralSubstitutionPattern ∧
    fullereneChiralityType? iupacP93CanonicalFullereneC60Type3ExpectedTest =
        some .noninherentlyChiralSubstitutionPattern ∧
    fullereneChiralityType? iupacP93CanonicalFullereneC70Type4ExpectedTest =
        some .chiralSubstituentsOnly ∧
    fullereneChiralityType? iupacP93CanonicalFullereneC70SuperimposedExpectedTest =
        some .inherentlyChiralSubstitutionPattern := by
  exact ⟨(fullereneChiralityType?_eq_some_iff _ _).2
      iupacP93CanonicalFullereneRelationalTypes_all_match.1,
    (fullereneChiralityType?_eq_some_iff _ _).2
      iupacP93CanonicalFullereneRelationalTypes_all_match.2.1,
    (fullereneChiralityType?_eq_some_iff _ _).2
      iupacP93CanonicalFullereneRelationalTypes_all_match.2.2.1,
    (fullereneChiralityType?_eq_some_iff _ _).2
      iupacP93CanonicalFullereneRelationalTypes_all_match.2.2.2.1,
    (fullereneChiralityType?_eq_some_iff _ _).2
      iupacP93CanonicalFullereneRelationalTypes_all_match.2.2.2.2⟩

theorem iupacP93CanonicalFullereneC76Type1DerivedClassifier_exact :
    fullereneChiralityType?
        (deriveMolecularFullereneRelationalSubstitutionTest
          iupacP93CanonicalFullereneC76Type1Molecule
          iupacP93CanonicalFullereneC76DerivativeTopologyInput
          iupacP93CanonicalFullereneC76Type1RelationalEvidence) =
      some .inherentlyChiralParent := by
  rw [iupacP93CanonicalFullereneC76Type1RelationalTest_exact]
  exact iupacP93CanonicalFullereneRelationalClassifier_all_exact.1

theorem iupacP93CanonicalFullereneC60Type2DerivedClassifier_exact :
    fullereneChiralityType?
        (deriveMolecularFullereneRelationalSubstitutionTest
          iupacP93CanonicalFullereneC60Type2Molecule
          iupacP93CanonicalFullereneC60DerivativeTopologyInput
          iupacP93CanonicalFullereneC60Type2RelationalEvidence) =
      some .inherentlyChiralSubstitutionPattern := by
  rw [iupacP93CanonicalFullereneC60Type2RelationalTest_exact]
  exact iupacP93CanonicalFullereneRelationalClassifier_all_exact.2.1

theorem iupacP93CanonicalFullereneC60Type3DerivedClassifier_exact :
    fullereneChiralityType?
        (deriveMolecularFullereneRelationalSubstitutionTest
          iupacP93CanonicalFullereneC60Type3Molecule
          iupacP93CanonicalFullereneC60DerivativeTopologyInput
          iupacP93CanonicalFullereneC60Type3RelationalEvidence) =
      some .noninherentlyChiralSubstitutionPattern := by
  rw [iupacP93CanonicalFullereneC60Type3RelationalTest_exact]
  exact iupacP93CanonicalFullereneRelationalClassifier_all_exact.2.2.1

theorem iupacP93CanonicalFullereneC70Type4DerivedClassifier_exact :
    fullereneChiralityType?
        (deriveMolecularFullereneRelationalSubstitutionTest
          iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
          iupacP93CanonicalFullereneC70DerivativeInput
          iupacP93CanonicalFullereneC70Type4RelationalEvidence) =
      some .chiralSubstituentsOnly := by
  rw [iupacP93CanonicalFullereneC70Type4RelationalTest_exact]
  exact iupacP93CanonicalFullereneRelationalClassifier_all_exact.2.2.2.1

theorem iupacP93CanonicalFullereneC70SuperimposedDerivedClassifier_exact :
    fullereneChiralityType?
        (deriveMolecularFullereneRelationalSubstitutionTest
          iupacP93CanonicalFullereneC70SuperimposedMolecule
          iupacP93CanonicalFullereneC70SuperimposedTopologyInput
          iupacP93CanonicalFullereneC70SuperimposedRelationalEvidence) =
      some .inherentlyChiralSubstitutionPattern := by
  rw [iupacP93CanonicalFullereneC70SuperimposedRelationalTest_exact]
  exact iupacP93CanonicalFullereneRelationalClassifier_all_exact.2.2.2.2

/-- Direct computation endpoint over the five actual derived tests, not proxy records.  Source
authorization is deliberately enforced later at the authority-observation boundary. -/
theorem iupacP93CanonicalFullereneDerivedClassifiers_all_exact :
    fullereneChiralityType?
        (deriveMolecularFullereneRelationalSubstitutionTest
          iupacP93CanonicalFullereneC76Type1Molecule
          iupacP93CanonicalFullereneC76DerivativeTopologyInput
          iupacP93CanonicalFullereneC76Type1RelationalEvidence) =
        some .inherentlyChiralParent ∧
    fullereneChiralityType?
        (deriveMolecularFullereneRelationalSubstitutionTest
          iupacP93CanonicalFullereneC60Type2Molecule
          iupacP93CanonicalFullereneC60DerivativeTopologyInput
          iupacP93CanonicalFullereneC60Type2RelationalEvidence) =
        some .inherentlyChiralSubstitutionPattern ∧
    fullereneChiralityType?
        (deriveMolecularFullereneRelationalSubstitutionTest
          iupacP93CanonicalFullereneC60Type3Molecule
          iupacP93CanonicalFullereneC60DerivativeTopologyInput
          iupacP93CanonicalFullereneC60Type3RelationalEvidence) =
        some .noninherentlyChiralSubstitutionPattern ∧
    fullereneChiralityType?
        (deriveMolecularFullereneRelationalSubstitutionTest
          iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
          iupacP93CanonicalFullereneC70DerivativeInput
          iupacP93CanonicalFullereneC70Type4RelationalEvidence) =
        some .chiralSubstituentsOnly ∧
    fullereneChiralityType?
        (deriveMolecularFullereneRelationalSubstitutionTest
          iupacP93CanonicalFullereneC70SuperimposedMolecule
          iupacP93CanonicalFullereneC70SuperimposedTopologyInput
          iupacP93CanonicalFullereneC70SuperimposedRelationalEvidence) =
        some .inherentlyChiralSubstitutionPattern :=
  ⟨iupacP93CanonicalFullereneC76Type1DerivedClassifier_exact,
    iupacP93CanonicalFullereneC60Type2DerivedClassifier_exact,
    iupacP93CanonicalFullereneC60Type3DerivedClassifier_exact,
    iupacP93CanonicalFullereneC70Type4DerivedClassifier_exact,
    iupacP93CanonicalFullereneC70SuperimposedDerivedClassifier_exact⟩

end
end P93CanonicalProgramFullerene
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.compiledDerivative_parentColoringChiral_iff
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneRelationalTests_all_exact
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneDerivedClassifiers_all_exact
