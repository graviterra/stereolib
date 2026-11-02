import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC70DerivativeReversingAudit

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

abbrev iupacP93CanonicalFullereneC70Type4FirstAddend : MolecularFullereneAddend :=
  iupacP93CanonicalFullereneC70Type4Assembly.compiledPlacedAddend 0
    iupacP93CanonicalFullereneC70Type4FirstPlacement.toPlaced

abbrev iupacP93CanonicalFullereneC70Type4SecondAddend : MolecularFullereneAddend :=
  iupacP93CanonicalFullereneC70Type4Assembly.compiledPlacedAddend 1
    iupacP93CanonicalFullereneC70Type4SecondPlacement.toPlaced

theorem iupacP93CanonicalFullereneC70Type4PlacementSites_exact :
    iupacP93CanonicalFullereneC70Type4FirstPlacement.attachmentSite
        ⟨0, by decide⟩ = 7 ∧
      iupacP93CanonicalFullereneC70Type4FirstPlacement.attachmentSite
        ⟨1, by decide⟩ = 24 ∧
      iupacP93CanonicalFullereneC70Type4SecondPlacement.attachmentSite
        ⟨0, by decide⟩ = 15 ∧
      iupacP93CanonicalFullereneC70Type4SecondPlacement.attachmentSite
        ⟨1, by decide⟩ = 34 := by
  have firstSorted :
      ({7, 24} : Finset Nat).sort (· ≤ ·) = [7, 24] := by
    rw [Finset.sort_insert]
    · simp
    · simp
    · simp
  have secondSorted :
      ({15, 34} : Finset Nat).sort (· ≤ ·) = [15, 34] := by
    rw [Finset.sort_insert]
    · simp
    · simp
    · simp
  simp [iupacP93CanonicalFullereneC70Type4FirstPlacement,
    iupacP93CanonicalFullereneC70Type4SecondPlacement,
    compileIUPACP93PrintedFullerenePlacementOf,
    iupacP93PrintedFullereneAttachmentSite,
    iupacP93PrintedFullereneSortedAttachmentSites,
    IUPACP93PrintedFullereneAddendKind.localTemplate_portCount,
    firstSorted, secondSorted]

theorem iupacP93CanonicalFullereneC70Type4_firstAlongSelf :
    iupacP93CanonicalFullereneC70Type4FirstAddend.ConstitutionallyIsomorphicAlong
      iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
      iupacP93CanonicalFullereneC70DerivativeInput
      iupacP93CanonicalFullereneC70Type4ReversingSymmetry
      iupacP93CanonicalFullereneC70Type4FirstAddend := by
  apply iupacP93CanonicalFullereneC70Type4Assembly
    |>.compiledAddends_constitutionallyIsomorphicAlong_of_sameTemplate
      iupacP93CanonicalFullereneC70Core_wellFormed
      iupacP93CanonicalFullereneDerivativeAssemblies_bondRecordsUnique.2.2.2.1
      iupacP93CanonicalFullereneC70Type4ReversingSymmetry
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate
      0 0 iupacP93CanonicalFullereneC70Type4FirstPlacement
      iupacP93CanonicalFullereneC70Type4FirstPlacement rfl rfl
  intro port
  have portCountExact :
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate.portCount = 2 := by
    decide
  have portBound : port.val < 2 := by simpa [portCountExact] using port.isLt
  rcases (show port.val = 0 ∨ port.val = 1 by omega) with portZero | portOne
  · have portEq : port = ⟨0, by rw [portCountExact]; decide⟩ := Fin.ext portZero
    subst port
    rw [iupacP93CanonicalFullereneC70Type4PlacementSites_exact.1]
    exact iupacP93CanonicalFullereneC70Type4ReversingSymmetry_fixedSites.1
  · have portEq : port = ⟨1, by rw [portCountExact]; decide⟩ := Fin.ext portOne
    subst port
    rw [iupacP93CanonicalFullereneC70Type4PlacementSites_exact.2.1]
    exact iupacP93CanonicalFullereneC70Type4ReversingSymmetry_fixedSites.2.1

theorem iupacP93CanonicalFullereneC70Type4_secondAlongSelf :
    iupacP93CanonicalFullereneC70Type4SecondAddend.ConstitutionallyIsomorphicAlong
      iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
      iupacP93CanonicalFullereneC70DerivativeInput
      iupacP93CanonicalFullereneC70Type4ReversingSymmetry
      iupacP93CanonicalFullereneC70Type4SecondAddend := by
  apply iupacP93CanonicalFullereneC70Type4Assembly
    |>.compiledAddends_constitutionallyIsomorphicAlong_of_sameTemplate
      iupacP93CanonicalFullereneC70Core_wellFormed
      iupacP93CanonicalFullereneDerivativeAssemblies_bondRecordsUnique.2.2.2.1
      iupacP93CanonicalFullereneC70Type4ReversingSymmetry
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate
      1 1 iupacP93CanonicalFullereneC70Type4SecondPlacement
      iupacP93CanonicalFullereneC70Type4SecondPlacement rfl rfl
  intro port
  have portCountExact :
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate.portCount = 2 := by
    decide
  have portBound : port.val < 2 := by simpa [portCountExact] using port.isLt
  rcases (show port.val = 0 ∨ port.val = 1 by omega) with portZero | portOne
  · have portEq : port = ⟨0, by rw [portCountExact]; decide⟩ := Fin.ext portZero
    subst port
    rw [iupacP93CanonicalFullereneC70Type4PlacementSites_exact.2.2.1]
    exact iupacP93CanonicalFullereneC70Type4ReversingSymmetry_fixedSites.2.2.1
  · have portEq : port = ⟨1, by rw [portCountExact]; decide⟩ := Fin.ext portOne
    subst port
    rw [iupacP93CanonicalFullereneC70Type4PlacementSites_exact.2.2.2]
    exact iupacP93CanonicalFullereneC70Type4ReversingSymmetry_fixedSites.2.2.2

theorem iupacP93CanonicalFullereneC70Type4_actualPatternPreserved :
    MolecularFullereneActualAddendPatternPreserved
      iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
      iupacP93CanonicalFullereneC70DerivativeInput
      iupacP93CanonicalFullereneC70Type4RelationalEvidence
      iupacP93CanonicalFullereneC70Type4ReversingSymmetry := by
  apply (molecularFullereneActualAddendPatternPreserved_two_iff
    iupacP93CanonicalFullereneC70Type4RelationalEvidence
    iupacP93CanonicalFullereneC70Type4ReversingSymmetry
    iupacP93CanonicalFullereneC70Type4FirstAddend
    iupacP93CanonicalFullereneC70Type4SecondAddend
    iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.2.1).mpr
  exact Or.inl ⟨iupacP93CanonicalFullereneC70Type4_firstAlongSelf,
    iupacP93CanonicalFullereneC70Type4_secondAlongSelf⟩

theorem iupacP93CanonicalFullereneC70Type4_sameTestPatternPreserved :
    MolecularFullereneSameTestAddendPatternPreserved
      iupacP93CanonicalFullereneC70Type4RelationalEvidence
      iupacP93CanonicalFullereneC70Type4ReversingSymmetry :=
  molecularFullereneActualAddendPatternPreserved_implies_sameTest
    iupacP93CanonicalFullereneC70Type4RelationalEvidence
    iupacP93CanonicalFullereneC70Type4ReversingSymmetry
    iupacP93CanonicalFullereneC70Type4_actualPatternPreserved

theorem iupacP93CanonicalFullereneC70Type4_actualPattern_achiral :
    ¬MolecularFullereneActualAddendPatternChiral
      iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
      iupacP93CanonicalFullereneC70DerivativeInput
      iupacP93CanonicalFullereneC70Type4RelationalEvidence := by
  rintro ⟨_oriented, rejects⟩
  exact rejects ⟨iupacP93CanonicalFullereneC70Type4ReversingSymmetry,
    iupacP93CanonicalFullereneC70Type4ReversingSymmetry_derivativeAutomorphism,
    iupacP93CanonicalFullereneC70Type4ReversingSymmetry_reversing,
    iupacP93CanonicalFullereneC70Type4_actualPatternPreserved⟩

theorem iupacP93CanonicalFullereneC70Type4_sameTestPattern_achiral :
    ¬MolecularFullereneSameTestAddendPatternChiral
      iupacP93CanonicalFullereneC70Type4RelationalEvidence := by
  rintro ⟨_oriented, rejects⟩
  exact rejects ⟨iupacP93CanonicalFullereneC70Type4ReversingSymmetry,
    iupacP93CanonicalFullereneC70Type4ReversingSymmetry_derivativeAutomorphism,
    iupacP93CanonicalFullereneC70Type4ReversingSymmetry_reversing,
    iupacP93CanonicalFullereneC70Type4_sameTestPatternPreserved⟩

end P93CanonicalProgramFullerene
end TetraStereo.OneCenter
