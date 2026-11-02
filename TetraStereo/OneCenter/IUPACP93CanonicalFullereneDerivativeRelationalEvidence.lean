import TetraStereo.OneCenter.IUPACP93CanonicalFullereneDerivativeAssemblies
import TetraStereo.OneCenter.P93MolecularFullereneTwoAddendSymmetry
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# Relational evidence for the five canonical P-93 fullerene derivatives

All five printed examples contain exactly two whole addends.  This module keeps their typed
template placements, proves the two generic identity-faithfulness collapses (same template or
different atom count), and instantiates the compiler-produced relational evidence.  No row may
supply external atom offsets, attachment ports, constitutional isomorphisms, or partition facts.
-/

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

noncomputable section

private abbrev PlacementOf :=
  MolecularFullereneAddendTemplateAssembly.MolecularFullerenePlacementOf

/-! ## Three core graph facts, inherited by all five assemblies -/

private theorem NumberedFaceTranscription.cageMolecule_wellFormed_of_certificate
    (transcription : NumberedFaceTranscription)
    (certificate : transcription.numberedPackage.Certificate transcription.cageMolecule) :
    transcription.cageMolecule.WellFormed := by
  intro bond bondPresent
  simp only [NumberedFaceTranscription.cageMolecule, List.mem_map] at bondPresent
  obtain ⟨edge, edgePresent, rfl⟩ := bondPresent
  have edgeJudged :=
    (certificate.tableJudgment transcription.cageMolecule transcription.numberedPackage).2.2.1
      edge edgePresent
  have sourceBound : edge.1 < transcription.atomCount := by
    simpa [MolecularFullereneNumberedCagePackage.carrier,
      NumberedFaceTranscription.numberedPackage,
      NumberedFaceTranscription.atomsByLocant] using edgeJudged.2.1
  have targetBound : edge.2 < transcription.atomCount := by
    simpa [MolecularFullereneNumberedCagePackage.carrier,
      NumberedFaceTranscription.numberedPackage,
      NumberedFaceTranscription.atomsByLocant] using edgeJudged.2.2
  rw [RawMolecule.BondEndpointsOK]
  simpa [NumberedFaceTranscription.singleBond,
    NumberedFaceTranscription.cageMolecule, RawMolecule.atomCount] using
      (show edge.1 < transcription.atomCount ∧ edge.2 < transcription.atomCount ∧
        edge.1 ≠ edge.2 from
        ⟨sourceBound, targetBound, Nat.ne_of_lt edgeJudged.1⟩)

private theorem NumberedFaceTranscription.cageMolecule_bondRecordsUnique_of_certificate
    (transcription : NumberedFaceTranscription)
    (certificate : transcription.numberedPackage.Certificate transcription.cageMolecule) :
    transcription.cageMolecule.BondRecordsUnique := by
  have table := certificate.tableJudgment
    transcription.cageMolecule transcription.numberedPackage
  rw [RawMolecule.BondRecordsUnique, NumberedFaceTranscription.cageMolecule,
    List.map_map]
  apply table.2.1.map_on
  intro first firstPresent second secondPresent keysEqual
  have firstOrdered := table.2.2.1 first firstPresent |>.1
  have secondOrdered := table.2.2.1 second secondPresent |>.1
  simpa [Function.comp_apply, NumberedFaceTranscription.singleBond, RawBond.edgeKey,
    Nat.min_eq_left firstOrdered.le, Nat.max_eq_right firstOrdered.le,
    Nat.min_eq_left secondOrdered.le, Nat.max_eq_right secondOrdered.le] using keysEqual

theorem iupacP93CanonicalFullereneC60Core_wellFormed :
    iupacP93CanonicalFullereneC60Transcription.cageMolecule.WellFormed := by
  exact iupacP93CanonicalFullereneC60Transcription.cageMolecule_wellFormed_of_certificate
    iupacP93CanonicalFullereneC60Certificate

theorem iupacP93CanonicalFullereneC70Core_wellFormed :
    iupacP93CanonicalFullereneC70Transcription.cageMolecule.WellFormed := by
  exact iupacP93CanonicalFullereneC70Transcription.cageMolecule_wellFormed_of_certificate
    iupacP93CanonicalFullereneC70SharedNumberedCage.certificate

theorem iupacP93CanonicalFullereneC76Core_wellFormed :
    iupacP93CanonicalFullereneC76Transcription.cageMolecule.WellFormed := by
  exact iupacP93CanonicalFullereneC76Transcription.cageMolecule_wellFormed_of_certificate
    iupacP93CanonicalFullereneC76Certificate

theorem iupacP93CanonicalFullereneC60Core_bondRecordsUnique :
    iupacP93CanonicalFullereneC60Transcription.cageMolecule.BondRecordsUnique := by
  exact
    iupacP93CanonicalFullereneC60Transcription.cageMolecule_bondRecordsUnique_of_certificate
      iupacP93CanonicalFullereneC60Certificate

theorem iupacP93CanonicalFullereneC70Core_bondRecordsUnique :
    iupacP93CanonicalFullereneC70Transcription.cageMolecule.BondRecordsUnique := by
  exact
    iupacP93CanonicalFullereneC70Transcription.cageMolecule_bondRecordsUnique_of_certificate
      iupacP93CanonicalFullereneC70SharedNumberedCage.certificate

theorem iupacP93CanonicalFullereneC76Core_bondRecordsUnique :
    iupacP93CanonicalFullereneC76Transcription.cageMolecule.BondRecordsUnique := by
  exact
    iupacP93CanonicalFullereneC76Transcription.cageMolecule_bondRecordsUnique_of_certificate
      iupacP93CanonicalFullereneC76Certificate

/-! ## Generic two-template identity collapses -/

/-- If both members of an exact two-addend assembly use the same template, their common positive
identity class is faithful to constitutional isomorphism by one generic compiler theorem. -/
theorem identityClassesFaithful_of_two_sameTemplate
    {core : RawMolecule} {carrier : Finset Nat}
    (assembly : MolecularFullereneAddendTemplateAssembly core carrier)
    (coreWellFormed : core.WellFormed)
    (bondRecordsUnique : assembly.compileExtension.assemble.BondRecordsUnique)
    (template : MolecularFullereneLocalAddendTemplate)
    (first second : PlacementOf carrier template)
    (firstAt : assembly.placements[0]? = some first.toPlaced)
    (secondAt : assembly.placements[1]? = some second.toPlaced)
    (addendsExact : assembly.compiledAddends =
      [assembly.compiledPlacedAddend 0 first.toPlaced,
        assembly.compiledPlacedAddend 1 second.toPlaced]) :
    ∀ left ∈ assembly.compiledAddends, ∀ right ∈ assembly.compiledAddends,
      left.identityClass = right.identityClass ↔
        left.ConstitutionallyIsomorphic assembly.compileExtension.assemble right := by
  let firstAddend := assembly.compiledPlacedAddend 0 first.toPlaced
  let secondAddend := assembly.compiledPlacedAddend 1 second.toPlaced
  have firstFirst : firstAddend.ConstitutionallyIsomorphic
      assembly.compileExtension.assemble firstAddend :=
    assembly.compiledAddends_constitutionallyIsomorphic_of_sameTemplate coreWellFormed
      bondRecordsUnique template 0 0 first first firstAt firstAt
  have firstSecond : firstAddend.ConstitutionallyIsomorphic
      assembly.compileExtension.assemble secondAddend :=
    assembly.compiledAddends_constitutionallyIsomorphic_of_sameTemplate coreWellFormed
      bondRecordsUnique template 0 1 first second firstAt secondAt
  have secondFirst : secondAddend.ConstitutionallyIsomorphic
      assembly.compileExtension.assemble firstAddend :=
    assembly.compiledAddends_constitutionallyIsomorphic_of_sameTemplate coreWellFormed
      bondRecordsUnique template 1 0 second first secondAt firstAt
  have secondSecond : secondAddend.ConstitutionallyIsomorphic
      assembly.compileExtension.assemble secondAddend :=
    assembly.compiledAddends_constitutionallyIsomorphic_of_sameTemplate coreWellFormed
      bondRecordsUnique template 1 1 second second secondAt secondAt
  intro left leftPresent right rightPresent
  rw [addendsExact] at leftPresent rightPresent
  simp only [List.mem_cons, List.not_mem_nil, or_false] at leftPresent rightPresent
  rcases leftPresent with rfl | rfl <;> rcases rightPresent with rfl | rfl
  · exact ⟨fun _ => firstFirst, fun _ => rfl⟩
  · exact ⟨fun _ => firstSecond, fun _ => rfl⟩
  · exact ⟨fun _ => secondFirst, fun _ => rfl⟩
  · exact ⟨fun _ => secondSecond, fun _ => rfl⟩

/-- For an exact two-addend assembly whose templates have different atom counts and different
identity classes, the compiler proves that the cross cases are impossible. -/
theorem identityClassesFaithful_of_two_differentAtomCounts
    {core : RawMolecule} {carrier : Finset Nat}
    (assembly : MolecularFullereneAddendTemplateAssembly core carrier)
    (coreWellFormed : core.WellFormed)
    (bondRecordsUnique : assembly.compileExtension.assemble.BondRecordsUnique)
    (firstTemplate secondTemplate : MolecularFullereneLocalAddendTemplate)
    (first : PlacementOf carrier firstTemplate)
    (second : PlacementOf carrier secondTemplate)
    (firstAt : assembly.placements[0]? = some first.toPlaced)
    (secondAt : assembly.placements[1]? = some second.toPlaced)
    (identityDifferent : firstTemplate.identityClass ≠ secondTemplate.identityClass)
    (atomCountsDifferent : firstTemplate.externalAtoms.length ≠
      secondTemplate.externalAtoms.length)
    (addendsExact : assembly.compiledAddends =
      [assembly.compiledPlacedAddend 0 first.toPlaced,
        assembly.compiledPlacedAddend 1 second.toPlaced]) :
    ∀ left ∈ assembly.compiledAddends, ∀ right ∈ assembly.compiledAddends,
      left.identityClass = right.identityClass ↔
        left.ConstitutionallyIsomorphic assembly.compileExtension.assemble right := by
  let firstAddend := assembly.compiledPlacedAddend 0 first.toPlaced
  let secondAddend := assembly.compiledPlacedAddend 1 second.toPlaced
  have firstIso : firstAddend.ConstitutionallyIsomorphic
      assembly.compileExtension.assemble firstAddend :=
    assembly.compiledAddends_constitutionallyIsomorphic_of_sameTemplate coreWellFormed
      bondRecordsUnique firstTemplate 0 0 first first firstAt firstAt
  have secondIso : secondAddend.ConstitutionallyIsomorphic
      assembly.compileExtension.assemble secondAddend :=
    assembly.compiledAddends_constitutionallyIsomorphic_of_sameTemplate coreWellFormed
      bondRecordsUnique secondTemplate 1 1 second second secondAt secondAt
  have crossNotIso : ¬firstAddend.ConstitutionallyIsomorphic
      assembly.compileExtension.assemble secondAddend :=
    assembly.compiledAddends_not_constitutionallyIsomorphic_of_atomCount_ne
      0 1 first.toPlaced second.toPlaced atomCountsDifferent
  have reverseNotIso : ¬secondAddend.ConstitutionallyIsomorphic
      assembly.compileExtension.assemble firstAddend :=
    assembly.compiledAddends_not_constitutionallyIsomorphic_of_atomCount_ne
      1 0 second.toPlaced first.toPlaced (Ne.symm atomCountsDifferent)
  intro left leftPresent right rightPresent
  rw [addendsExact] at leftPresent rightPresent
  simp only [List.mem_cons, List.not_mem_nil, or_false] at leftPresent rightPresent
  rcases leftPresent with rfl | rfl <;> rcases rightPresent with rfl | rfl
  · exact ⟨fun _ => firstIso, fun _ => rfl⟩
  · exact ⟨fun equality => False.elim (identityDifferent equality),
      fun isomorphic => False.elim (crossNotIso isomorphic)⟩
  · exact ⟨fun equality => False.elim (identityDifferent equality.symm),
      fun isomorphic => False.elim (reverseNotIso isomorphic)⟩
  · exact ⟨fun _ => secondIso, fun _ => rfl⟩

/-- If the compiler finds no intrinsically chiral addend, chirality classification is faithful
for every constitutional identity class. -/
theorem chiralIdentityFaithful_of_compiledChiralAddends_empty
    {core : RawMolecule} {carrier : Finset Nat}
    (assembly : MolecularFullereneAddendTemplateAssembly core carrier)
    (empty : assembly.compiledChiralAddends = ∅) :
    ∀ first ∈ assembly.compiledAddends, ∀ second ∈ assembly.compiledAddends,
      first.identityClass = second.identityClass →
        (first ∈ assembly.compiledChiralAddends ↔
          second ∈ assembly.compiledChiralAddends) := by
  intro first _ second _ _
  rw [empty]
  simp

/-- If both exact compiled addends are intrinsically chiral, classification is again faithful
without a row-authored identity ledger. -/
theorem chiralIdentityFaithful_of_compiledChiralAddends_all
    {core : RawMolecule} {carrier : Finset Nat}
    (assembly : MolecularFullereneAddendTemplateAssembly core carrier)
    (all : assembly.compiledChiralAddends = assembly.compiledAddends.toFinset) :
    ∀ first ∈ assembly.compiledAddends, ∀ second ∈ assembly.compiledAddends,
      first.identityClass = second.identityClass →
        (first ∈ assembly.compiledChiralAddends ↔
          second ∈ assembly.compiledChiralAddends) := by
  intro first firstPresent second secondPresent _
  rw [all]
  simp [firstPresent, secondPresent]

/-! ## Ten typed source placements -/

def iupacP93CanonicalFullereneC76Type1TertButylPlacement :
    PlacementOf iupacP93CanonicalFullereneC76Transcription.numberedPackage.carrier
      iupacP93CanonicalFullereneTertButylTemplate :=
  @compileIUPACP93PrintedFullerenePlacementOf
    iupacP93CanonicalFullereneC76Transcription.cageMolecule
    iupacP93CanonicalFullereneC76Transcription.numberedPackage.carrier rfl
    { kind := .tertButyl, attachmentSites := {19} }
    (iupacP93CanonicalFullereneC76Type1Placements_audited.2.2.1 _ (by
      simp [iupacP93CanonicalFullereneC76Type1Placements])) (by decide)

def iupacP93CanonicalFullereneC76Type1HydrogenPlacement :
    PlacementOf iupacP93CanonicalFullereneC76Transcription.numberedPackage.carrier
      iupacP93CanonicalFullereneHydrogenTemplate :=
  @compileIUPACP93PrintedFullerenePlacementOf
    iupacP93CanonicalFullereneC76Transcription.cageMolecule
    iupacP93CanonicalFullereneC76Transcription.numberedPackage.carrier rfl
    { kind := .hydrogen, attachmentSites := {20} }
    (iupacP93CanonicalFullereneC76Type1Placements_audited.2.2.1 _ (by
      simp [iupacP93CanonicalFullereneC76Type1Placements])) (by decide)

def iupacP93CanonicalFullereneC60Type2FirstPlacement :
    PlacementOf iupacP93CanonicalFullereneC60Transcription.numberedPackage.carrier
      iupacP93CanonicalFullereneTrisilylTemplate :=
  @compileIUPACP93PrintedFullerenePlacementOf
    iupacP93CanonicalFullereneC60Transcription.cageMolecule
    iupacP93CanonicalFullereneC60Transcription.numberedPackage.carrier rfl
    { kind := .trisilyl, attachmentSites := {0} }
    (iupacP93CanonicalFullereneC60Type2Placements_audited.2.2.1 _ (by
      simp [iupacP93CanonicalFullereneC60Type2Placements])) (by decide)

def iupacP93CanonicalFullereneC60Type2SecondPlacement :
    PlacementOf iupacP93CanonicalFullereneC60Transcription.numberedPackage.carrier
      iupacP93CanonicalFullereneTrisilylTemplate :=
  @compileIUPACP93PrintedFullerenePlacementOf
    iupacP93CanonicalFullereneC60Transcription.cageMolecule
    iupacP93CanonicalFullereneC60Transcription.numberedPackage.carrier rfl
    { kind := .trisilyl, attachmentSites := {22} }
    (iupacP93CanonicalFullereneC60Type2Placements_audited.2.2.1 _ (by
      simp [iupacP93CanonicalFullereneC60Type2Placements])) (by decide)

def iupacP93CanonicalFullereneC60Type3TertButylPlacement :
    PlacementOf iupacP93CanonicalFullereneC60Transcription.numberedPackage.carrier
      iupacP93CanonicalFullereneTertButylTemplate :=
  @compileIUPACP93PrintedFullerenePlacementOf
    iupacP93CanonicalFullereneC60Transcription.cageMolecule
    iupacP93CanonicalFullereneC60Transcription.numberedPackage.carrier rfl
    { kind := .tertButyl, attachmentSites := {0} }
    (iupacP93CanonicalFullereneC60Type3Placements_audited.2.2.1 _ (by
      simp [iupacP93CanonicalFullereneC60Type3Placements])) (by decide)

def iupacP93CanonicalFullereneC60Type3DicyclopropylPlacement :
    PlacementOf iupacP93CanonicalFullereneC60Transcription.numberedPackage.carrier
      iupacP93CanonicalFullereneDicyclopropylCycloheptatrienylTemplate :=
  @compileIUPACP93PrintedFullerenePlacementOf
    iupacP93CanonicalFullereneC60Transcription.cageMolecule
    iupacP93CanonicalFullereneC60Transcription.numberedPackage.carrier rfl
    { kind := .dicyclopropylCycloheptatrienyl, attachmentSites := {6} }
    (iupacP93CanonicalFullereneC60Type3Placements_audited.2.2.1 _ (by
      simp [iupacP93CanonicalFullereneC60Type3Placements])) (by decide)

def iupacP93CanonicalFullereneC70Type4FirstPlacement :
    PlacementOf iupacP93CanonicalFullereneC70Transcription.numberedPackage.carrier
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate :=
  @compileIUPACP93PrintedFullerenePlacementOf
    iupacP93CanonicalFullereneC70Transcription.cageMolecule
    iupacP93CanonicalFullereneC70Transcription.numberedPackage.carrier rfl
    { kind := .cyclopropanoBisCarboxylatePhenylbutyl, attachmentSites := {7, 24} }
    (iupacP93CanonicalFullereneC70Type4Placements_audited.2.2.1 _ (by
      simp [iupacP93CanonicalFullereneC70Type4Placements])) (by decide)

def iupacP93CanonicalFullereneC70Type4SecondPlacement :
    PlacementOf iupacP93CanonicalFullereneC70Transcription.numberedPackage.carrier
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate :=
  @compileIUPACP93PrintedFullerenePlacementOf
    iupacP93CanonicalFullereneC70Transcription.cageMolecule
    iupacP93CanonicalFullereneC70Transcription.numberedPackage.carrier rfl
    { kind := .cyclopropanoBisCarboxylatePhenylbutyl, attachmentSites := {15, 34} }
    (iupacP93CanonicalFullereneC70Type4Placements_audited.2.2.1 _ (by
      simp [iupacP93CanonicalFullereneC70Type4Placements])) (by decide)

def iupacP93CanonicalFullereneC70SuperimposedFirstPlacement :
    PlacementOf iupacP93CanonicalFullereneC70Transcription.numberedPackage.carrier
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate :=
  @compileIUPACP93PrintedFullerenePlacementOf
    iupacP93CanonicalFullereneC70Transcription.cageMolecule
    iupacP93CanonicalFullereneC70Transcription.numberedPackage.carrier rfl
    { kind := .cyclopropanoBisCarboxylatePhenylbutyl, attachmentSites := {7, 24} }
    (iupacP93CanonicalFullereneC70SuperimposedPlacements_audited.2.2.1 _ (by
      simp [iupacP93CanonicalFullereneC70SuperimposedPlacements])) (by decide)

def iupacP93CanonicalFullereneC70SuperimposedSecondPlacement :
    PlacementOf iupacP93CanonicalFullereneC70Transcription.numberedPackage.carrier
      iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate :=
  @compileIUPACP93PrintedFullerenePlacementOf
    iupacP93CanonicalFullereneC70Transcription.cageMolecule
    iupacP93CanonicalFullereneC70Transcription.numberedPackage.carrier rfl
    { kind := .cyclopropanoBisCarboxylatePhenylbutyl, attachmentSites := {32, 33} }
    (iupacP93CanonicalFullereneC70SuperimposedPlacements_audited.2.2.1 _ (by
      simp [iupacP93CanonicalFullereneC70SuperimposedPlacements])) (by decide)

/-! ## Exact compiled lists and inherited bond uniqueness -/

theorem iupacP93CanonicalFullereneDerivativeAssemblies_bondRecordsUnique :
    iupacP93CanonicalFullereneC76Type1Assembly.compileExtension.assemble.BondRecordsUnique ∧
      iupacP93CanonicalFullereneC60Type2Assembly.compileExtension.assemble.BondRecordsUnique ∧
      iupacP93CanonicalFullereneC60Type3Assembly.compileExtension.assemble.BondRecordsUnique ∧
      iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble.BondRecordsUnique ∧
      iupacP93CanonicalFullereneC70SuperimposedAssembly.compileExtension.assemble.BondRecordsUnique :=
  ⟨iupacP93CanonicalFullereneC76Type1Assembly.assembleBondRecordsUnique
      iupacP93CanonicalFullereneC76Core_wellFormed
      iupacP93CanonicalFullereneC76Core_bondRecordsUnique,
    iupacP93CanonicalFullereneC60Type2Assembly.assembleBondRecordsUnique
      iupacP93CanonicalFullereneC60Core_wellFormed
      iupacP93CanonicalFullereneC60Core_bondRecordsUnique,
    iupacP93CanonicalFullereneC60Type3Assembly.assembleBondRecordsUnique
      iupacP93CanonicalFullereneC60Core_wellFormed
      iupacP93CanonicalFullereneC60Core_bondRecordsUnique,
    iupacP93CanonicalFullereneC70Type4Assembly.assembleBondRecordsUnique
      iupacP93CanonicalFullereneC70Core_wellFormed
      iupacP93CanonicalFullereneC70Core_bondRecordsUnique,
    iupacP93CanonicalFullereneC70SuperimposedAssembly.assembleBondRecordsUnique
      iupacP93CanonicalFullereneC70Core_wellFormed
      iupacP93CanonicalFullereneC70Core_bondRecordsUnique⟩

theorem iupacP93CanonicalFullereneDerivativeCompiledAddends_exact :
    iupacP93CanonicalFullereneC76Type1Assembly.compiledAddends =
        [iupacP93CanonicalFullereneC76Type1Assembly.compiledPlacedAddend 0
            iupacP93CanonicalFullereneC76Type1TertButylPlacement.toPlaced,
          iupacP93CanonicalFullereneC76Type1Assembly.compiledPlacedAddend 1
            iupacP93CanonicalFullereneC76Type1HydrogenPlacement.toPlaced] ∧
      iupacP93CanonicalFullereneC60Type2Assembly.compiledAddends =
        [iupacP93CanonicalFullereneC60Type2Assembly.compiledPlacedAddend 0
            iupacP93CanonicalFullereneC60Type2FirstPlacement.toPlaced,
          iupacP93CanonicalFullereneC60Type2Assembly.compiledPlacedAddend 1
            iupacP93CanonicalFullereneC60Type2SecondPlacement.toPlaced] ∧
      iupacP93CanonicalFullereneC60Type3Assembly.compiledAddends =
        [iupacP93CanonicalFullereneC60Type3Assembly.compiledPlacedAddend 0
            iupacP93CanonicalFullereneC60Type3TertButylPlacement.toPlaced,
          iupacP93CanonicalFullereneC60Type3Assembly.compiledPlacedAddend 1
            iupacP93CanonicalFullereneC60Type3DicyclopropylPlacement.toPlaced] ∧
      iupacP93CanonicalFullereneC70Type4Assembly.compiledAddends =
        [iupacP93CanonicalFullereneC70Type4Assembly.compiledPlacedAddend 0
            iupacP93CanonicalFullereneC70Type4FirstPlacement.toPlaced,
          iupacP93CanonicalFullereneC70Type4Assembly.compiledPlacedAddend 1
            iupacP93CanonicalFullereneC70Type4SecondPlacement.toPlaced] ∧
      iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledAddends =
        [iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledPlacedAddend 0
            iupacP93CanonicalFullereneC70SuperimposedFirstPlacement.toPlaced,
          iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledPlacedAddend 1
            iupacP93CanonicalFullereneC70SuperimposedSecondPlacement.toPlaced] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Five identity and chiral-classification theorems -/

theorem iupacP93CanonicalFullereneC76Type1IdentityClassesFaithful :
    ∀ first ∈ iupacP93CanonicalFullereneC76Type1Assembly.compiledAddends,
      ∀ second ∈ iupacP93CanonicalFullereneC76Type1Assembly.compiledAddends,
        first.identityClass = second.identityClass ↔
          first.ConstitutionallyIsomorphic
            iupacP93CanonicalFullereneC76Type1Assembly.compileExtension.assemble second :=
  identityClassesFaithful_of_two_differentAtomCounts
    iupacP93CanonicalFullereneC76Type1Assembly
    iupacP93CanonicalFullereneC76Core_wellFormed
    iupacP93CanonicalFullereneDerivativeAssemblies_bondRecordsUnique.1
    iupacP93CanonicalFullereneTertButylTemplate
    iupacP93CanonicalFullereneHydrogenTemplate
    iupacP93CanonicalFullereneC76Type1TertButylPlacement
    iupacP93CanonicalFullereneC76Type1HydrogenPlacement rfl rfl
    (by decide) (by decide)
    iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.1

theorem iupacP93CanonicalFullereneC60Type2IdentityClassesFaithful :
    ∀ first ∈ iupacP93CanonicalFullereneC60Type2Assembly.compiledAddends,
      ∀ second ∈ iupacP93CanonicalFullereneC60Type2Assembly.compiledAddends,
        first.identityClass = second.identityClass ↔
          first.ConstitutionallyIsomorphic
            iupacP93CanonicalFullereneC60Type2Assembly.compileExtension.assemble second :=
  identityClassesFaithful_of_two_sameTemplate
    iupacP93CanonicalFullereneC60Type2Assembly
    iupacP93CanonicalFullereneC60Core_wellFormed
    iupacP93CanonicalFullereneDerivativeAssemblies_bondRecordsUnique.2.1
    iupacP93CanonicalFullereneTrisilylTemplate
    iupacP93CanonicalFullereneC60Type2FirstPlacement
    iupacP93CanonicalFullereneC60Type2SecondPlacement rfl rfl
    iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.1

theorem iupacP93CanonicalFullereneC60Type3IdentityClassesFaithful :
    ∀ first ∈ iupacP93CanonicalFullereneC60Type3Assembly.compiledAddends,
      ∀ second ∈ iupacP93CanonicalFullereneC60Type3Assembly.compiledAddends,
        first.identityClass = second.identityClass ↔
          first.ConstitutionallyIsomorphic
            iupacP93CanonicalFullereneC60Type3Assembly.compileExtension.assemble second :=
  identityClassesFaithful_of_two_differentAtomCounts
    iupacP93CanonicalFullereneC60Type3Assembly
    iupacP93CanonicalFullereneC60Core_wellFormed
    iupacP93CanonicalFullereneDerivativeAssemblies_bondRecordsUnique.2.2.1
    iupacP93CanonicalFullereneTertButylTemplate
    iupacP93CanonicalFullereneDicyclopropylCycloheptatrienylTemplate
    iupacP93CanonicalFullereneC60Type3TertButylPlacement
    iupacP93CanonicalFullereneC60Type3DicyclopropylPlacement rfl rfl
    (by decide) (by decide)
    iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.1

theorem iupacP93CanonicalFullereneC70Type4IdentityClassesFaithful :
    ∀ first ∈ iupacP93CanonicalFullereneC70Type4Assembly.compiledAddends,
      ∀ second ∈ iupacP93CanonicalFullereneC70Type4Assembly.compiledAddends,
        first.identityClass = second.identityClass ↔
          first.ConstitutionallyIsomorphic
            iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble second :=
  identityClassesFaithful_of_two_sameTemplate
    iupacP93CanonicalFullereneC70Type4Assembly
    iupacP93CanonicalFullereneC70Core_wellFormed
    iupacP93CanonicalFullereneDerivativeAssemblies_bondRecordsUnique.2.2.2.1
    iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate
    iupacP93CanonicalFullereneC70Type4FirstPlacement
    iupacP93CanonicalFullereneC70Type4SecondPlacement rfl rfl
    iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.2.1

theorem iupacP93CanonicalFullereneC70SuperimposedIdentityClassesFaithful :
    ∀ first ∈ iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledAddends,
      ∀ second ∈ iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledAddends,
        first.identityClass = second.identityClass ↔
          first.ConstitutionallyIsomorphic
            iupacP93CanonicalFullereneC70SuperimposedAssembly.compileExtension.assemble second :=
  identityClassesFaithful_of_two_sameTemplate
    iupacP93CanonicalFullereneC70SuperimposedAssembly
    iupacP93CanonicalFullereneC70Core_wellFormed
    iupacP93CanonicalFullereneDerivativeAssemblies_bondRecordsUnique.2.2.2.2
    iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate
    iupacP93CanonicalFullereneC70SuperimposedFirstPlacement
    iupacP93CanonicalFullereneC70SuperimposedSecondPlacement rfl rfl
    iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.2.2

theorem iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact :
    iupacP93CanonicalFullereneC76Type1Assembly.compiledChiralAddends = ∅ ∧
      iupacP93CanonicalFullereneC60Type2Assembly.compiledChiralAddends = ∅ ∧
      iupacP93CanonicalFullereneC60Type3Assembly.compiledChiralAddends = ∅ ∧
      iupacP93CanonicalFullereneC70Type4Assembly.compiledChiralAddends =
        iupacP93CanonicalFullereneC70Type4Assembly.compiledAddends.toFinset ∧
      iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledChiralAddends =
        iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledAddends.toFinset := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Five complete relational evidence values -/

noncomputable def iupacP93CanonicalFullereneC76Type1RelationalEvidence :
    MolecularFullereneAddendRelationalEvidence
      iupacP93CanonicalFullereneC76Type1Assembly.compileExtension.assemble
      iupacP93CanonicalFullereneC76Transcription.numberedPackage.topologyInput.carrier :=
  @MolecularFullereneAddendTemplateAssembly.toRelationalEvidence
    iupacP93CanonicalFullereneC76Transcription.cageMolecule
    iupacP93CanonicalFullereneC76Transcription.numberedPackage.topologyInput.carrier
    iupacP93CanonicalFullereneC76Type1Assembly
    (show iupacP93CanonicalFullereneC76Type1Assembly.placements ≠ [] from by decide)
    iupacP93CanonicalFullereneC76Core_wellFormed true
    iupacP93CanonicalFullereneC76Type1IdentityClassesFaithful
    (chiralIdentityFaithful_of_compiledChiralAddends_empty _
      iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.1)

noncomputable def iupacP93CanonicalFullereneC60Type2RelationalEvidence :
    MolecularFullereneAddendRelationalEvidence
      iupacP93CanonicalFullereneC60Type2Assembly.compileExtension.assemble
      iupacP93CanonicalFullereneC60Transcription.numberedPackage.topologyInput.carrier :=
  @MolecularFullereneAddendTemplateAssembly.toRelationalEvidence
    iupacP93CanonicalFullereneC60Transcription.cageMolecule
    iupacP93CanonicalFullereneC60Transcription.numberedPackage.topologyInput.carrier
    iupacP93CanonicalFullereneC60Type2Assembly
    (show iupacP93CanonicalFullereneC60Type2Assembly.placements ≠ [] from by decide)
    iupacP93CanonicalFullereneC60Core_wellFormed true
    iupacP93CanonicalFullereneC60Type2IdentityClassesFaithful
    (chiralIdentityFaithful_of_compiledChiralAddends_empty _
      iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.2.1)

noncomputable def iupacP93CanonicalFullereneC60Type3RelationalEvidence :
    MolecularFullereneAddendRelationalEvidence
      iupacP93CanonicalFullereneC60Type3Assembly.compileExtension.assemble
      iupacP93CanonicalFullereneC60Transcription.numberedPackage.topologyInput.carrier :=
  @MolecularFullereneAddendTemplateAssembly.toRelationalEvidence
    iupacP93CanonicalFullereneC60Transcription.cageMolecule
    iupacP93CanonicalFullereneC60Transcription.numberedPackage.topologyInput.carrier
    iupacP93CanonicalFullereneC60Type3Assembly
    (show iupacP93CanonicalFullereneC60Type3Assembly.placements ≠ [] from by decide)
    iupacP93CanonicalFullereneC60Core_wellFormed true
    iupacP93CanonicalFullereneC60Type3IdentityClassesFaithful
    (chiralIdentityFaithful_of_compiledChiralAddends_empty _
      iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.2.2.1)

noncomputable def iupacP93CanonicalFullereneC70Type4RelationalEvidence :
    MolecularFullereneAddendRelationalEvidence
      iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
      iupacP93CanonicalFullereneC70Transcription.numberedPackage.topologyInput.carrier :=
  @MolecularFullereneAddendTemplateAssembly.toRelationalEvidence
    iupacP93CanonicalFullereneC70Transcription.cageMolecule
    iupacP93CanonicalFullereneC70Transcription.numberedPackage.topologyInput.carrier
    iupacP93CanonicalFullereneC70Type4Assembly
    (show iupacP93CanonicalFullereneC70Type4Assembly.placements ≠ [] from by decide)
    iupacP93CanonicalFullereneC70Core_wellFormed true
    iupacP93CanonicalFullereneC70Type4IdentityClassesFaithful
    (chiralIdentityFaithful_of_compiledChiralAddends_all _
      iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.2.2.2.1)

noncomputable def iupacP93CanonicalFullereneC70SuperimposedRelationalEvidence :
    MolecularFullereneAddendRelationalEvidence
      iupacP93CanonicalFullereneC70SuperimposedAssembly.compileExtension.assemble
      iupacP93CanonicalFullereneC70Transcription.numberedPackage.topologyInput.carrier :=
  @MolecularFullereneAddendTemplateAssembly.toRelationalEvidence
    iupacP93CanonicalFullereneC70Transcription.cageMolecule
    iupacP93CanonicalFullereneC70Transcription.numberedPackage.topologyInput.carrier
    iupacP93CanonicalFullereneC70SuperimposedAssembly
    (show iupacP93CanonicalFullereneC70SuperimposedAssembly.placements ≠ [] from by decide)
    iupacP93CanonicalFullereneC70Core_wellFormed true
    iupacP93CanonicalFullereneC70SuperimposedIdentityClassesFaithful
    (chiralIdentityFaithful_of_compiledChiralAddends_all _
      iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.2.2.2.2)

end
end P93CanonicalProgramFullerene
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.identityClassesFaithful_of_two_sameTemplate
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.identityClassesFaithful_of_two_differentAtomCounts
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneDerivativeAssemblies_bondRecordsUnique
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneDerivativeCompiledAddends_exact
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC76Type1IdentityClassesFaithful
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC60Type2IdentityClassesFaithful
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC60Type3IdentityClassesFaithful
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC70Type4IdentityClassesFaithful
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC70SuperimposedIdentityClassesFaithful
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC76Type1RelationalEvidence
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC60Type2RelationalEvidence
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC60Type3RelationalEvidence
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC70Type4RelationalEvidence
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.iupacP93CanonicalFullereneC70SuperimposedRelationalEvidence
