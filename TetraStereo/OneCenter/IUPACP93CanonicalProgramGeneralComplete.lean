import TetraStereo.OneCenter.IUPACP93CanonicalProgramGeneral

set_option autoImplicit false

/-!
# Complete provenance-bearing P-93.1 source program

This module adds the P-93.1.4 `ambo` example to the four previously transcribed general rows.
The constitution is the complete 31-heavy-atom graph of the printed alpha-tocopherol example.
The authority says only "plus a proportion of the epimer at C-2"; consequently the payload records
qualitative non-equimolar composition and does not invent a numerical mole fraction.
-/

namespace TetraStereo.OneCenter

open BlueBookP93
open IUPACNormativeProvision
open P93CanonicalProgramGeneral

namespace P93CanonicalProgramGeneralComplete

/-!
## P-93.1.4: `2-ambo-(2R,4'R,8'R)-alpha-tocopherol`

Atom indexing follows the printed systematic name:

* 0 is O-1; 1-3 are C-2 through C-4 of the chroman ring;
* 4-9 are the fused benzene carbons C-4a, C-5, C-6, C-7, C-8, C-8a;
* 10 is the C-2 methyl; 11-23 are the tridecyl C-1' through C-13';
* 24-26 are the C-4', C-8', and C-12' methyl groups;
* 27-29 are the C-5, C-7, and C-8 methyl groups; 30 is the C-6 hydroxy oxygen.
-/
def amboSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms :=
        [ oxygenAtom
        , carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom
        , carbonAtom, carbonAtom, carbonAtom, carbonAtom
        , carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom
        , carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom
        , carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom
        , carbonAtom, oxygenAtom ]
      interactions :=
        [ bond 0 1, bond 1 2, bond 2 3, bond 3 4
        , bond 4 5 2, bond 5 6, bond 6 7 2, bond 7 8, bond 8 9 2, bond 9 4
        , bond 9 0
        , bond 1 10, bond 1 11
        , bond 11 12, bond 12 13, bond 13 14, bond 14 15, bond 15 16
        , bond 16 17, bond 17 18, bond 18 19, bond 19 20, bond 20 21
        , bond 21 22, bond 22 23
        , bond 14 24, bond 18 25, bond 22 26
        , bond 5 27, bond 7 28, bond 8 29, bond 6 30 ] }

@[simp] theorem amboSource_atomCount : amboSource.molecule.atomCount = 31 := rfl

@[simp] theorem amboSource_interactionCount : amboSource.molecule.interactions.length = 32 := rfl

theorem amboSource_structurallyWellFormed : amboSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff amboSource).mp
    (by decide)

theorem amboCenter2_envelope :
    P93CanonicalPhysicalUnitEnvelope amboSource (.atomCenter 1) := by
  refine ⟨by decide, [0, 2, 10, 11], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, amboSource, SemanticMolecule.atomCount]
  intro neighbor member
  simp at member
  rcases member with rfl | rfl | rfl | rfl <;> left <;>
    simp [P93AuthorityBinaryBond, amboSource, bond,
      P93AuthorityBinaryInteractionKind]

theorem amboCenter4Prime_envelope :
    P93CanonicalPhysicalUnitEnvelope amboSource (.atomCenter 14) := by
  refine ⟨by decide, [13, 15, 24], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, amboSource, SemanticMolecule.atomCount]
  intro neighbor member
  simp at member
  rcases member with rfl | rfl | rfl <;> left <;>
    simp [P93AuthorityBinaryBond, amboSource, bond,
      P93AuthorityBinaryInteractionKind]

theorem amboCenter8Prime_envelope :
    P93CanonicalPhysicalUnitEnvelope amboSource (.atomCenter 18) := by
  refine ⟨by decide, [17, 19, 25], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, amboSource, SemanticMolecule.atomCount]
  intro neighbor member
  simp at member
  rcases member with rfl | rfl | rfl <;> left <;>
    simp [P93AuthorityBinaryBond, amboSource, bond,
      P93AuthorityBinaryInteractionKind]

def primedAssignment (center locant primes : Nat)
    (descriptor : BlueBookP93.Acyclic.Descriptor) :
    P93AuthorityLocatedAssignment P93CanonicalDescriptor where
  unit := .atomCenter center
  citation := citation locant primes
  descriptor := .acyclic descriptor

def amboFirst : P93CanonicalGeneralConfiguration where
  assignments :=
    [ assignment 1 2 .R
    , primedAssignment 14 4 1 .R
    , primedAssignment 18 8 1 .R ]

def amboSecond : P93CanonicalGeneralConfiguration where
  assignments :=
    [ assignment 1 2 .S
    , primedAssignment 14 4 1 .R
    , primedAssignment 18 8 1 .R ]

def amboMixture :
    GeneralConfiguration.QualitativeBinaryMixture P93CanonicalGeneralConfiguration where
  first := amboFirst
  second := amboSecond
  composition := .nonEquimolar

def amboPayload : P93GeneralClausePayload .ambo :=
  .ambo (citation 2) amboMixture

theorem amboPayload_valid :
    (P93ClausePayloadData.general amboPayload).ValidFor amboSource := by
  constructor
  · intro claim member
    simp [P93ClausePayloadData.toClaims, amboPayload,
      P93GeneralClausePayload.toClaims, amboMixture, amboFirst, amboSecond,
      P93CanonicalGeneralConfiguration.toClaims] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by simp [assignment, citation, P93AuthorityCitationToken.Valid],
        amboCenter2_envelope⟩
    · exact amboCenter2_envelope
    · exact ⟨by simp [primedAssignment, citation, P93AuthorityCitationToken.Valid],
        amboCenter4Prime_envelope⟩
    · exact amboCenter4Prime_envelope
    · exact ⟨by simp [primedAssignment, citation, P93AuthorityCitationToken.Valid],
        amboCenter8Prime_envelope⟩
    · exact amboCenter8Prime_envelope
    · exact ⟨by simp [assignment, citation, P93AuthorityCitationToken.Valid],
        amboCenter2_envelope⟩
    · exact amboCenter2_envelope
    · exact ⟨by simp [primedAssignment, citation, P93AuthorityCitationToken.Valid],
        amboCenter4Prime_envelope⟩
    · exact amboCenter4Prime_envelope
    · exact ⟨by simp [primedAssignment, citation, P93AuthorityCitationToken.Valid],
        amboCenter8Prime_envelope⟩
    · exact amboCenter8Prime_envelope
  · simp [amboPayload, P93GeneralClausePayload.Intrinsic, amboMixture,
      amboFirst, amboSecond, P93CanonicalGeneralConfiguration.StructurallyComplete,
      P93CanonicalGeneralInvertAt, assignment, primedAssignment, citation,
      P93CanonicalDescriptor.mirrorAction, P93CanonicalDescriptor.mirror,
      P93AuthorityConfiguration.RelativeEquivalent,
      P93AuthorityConfiguration.globallyMirrored]

def amboObservation : P93ClauseObservation amboSource (.general .ambo) where
  payload := .general amboPayload
  validFor := amboPayload_valid

def amboTranscription : P93CanonicalSourceTranscription amboSource
    (.general .ambo) amboObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 :=
    "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 37
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.1.4"
  clauseSectionExact := rfl
  observationSubsection := "P-93.1.4"
  observationSubsectionNonempty := by decide
  printedObservation :=
    "2-ambo-(2R,4′R,8′R)-α-tocopherol (refs. 37, 44); plus a proportion of the epimer at C-2"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro _claim _claimMember
    exact
      { supportingLocator := "PDF page 37, P-93.1.4, sole named example and complete adjacent structure"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "2-ambo-(2R,4′R,8′R)-α-tocopherol; figure labels 2R, 4′R, 8′R and states plus a proportion of the epimer at C-2"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def amboEntry : P93CanonicalClauseObservationEntry where
  source := amboSource
  sourceAdmitted := amboSource_structurallyWellFormed
  clause := .general .ambo
  clauseListed := by
    simp [P93Clause.all, Remaining71P93ClosedProductionRow.all,
      Remaining71P93ClosedProductionRow.generalRows,
      Remaining71P93GeneralAuthorityRow.all]
  observation := amboObservation
  transcription := amboTranscription

def entries : List P93CanonicalClauseObservationEntry :=
  P93CanonicalProgramGeneral.entries ++ [amboEntry]

def coveredClauses : List P93Clause := entries.map fun entry => entry.clause

@[simp] theorem entries_length : entries.length = 5 := rfl

@[simp] theorem coveredClauses_exact : coveredClauses =
    Remaining71P93GeneralAuthorityRow.all.map fun row => (.general row : P93Clause) := rfl

theorem coveredClauses_nodup : coveredClauses.Nodup := by
  rw [coveredClauses_exact]
  decide

theorem entry_keys_nodup :
    (entries.map fun entry => (entry.clause.family, entry.source)).Nodup := by
  decide

theorem entries_family_source_unique :
    ∀ first ∈ entries, ∀ second ∈ entries,
      first.source = second.source → first.clause.family = second.clause.family → first = second := by
  intro first firstMem second secondMem sourceEq familyEq
  exact (List.inj_on_of_nodup_map entry_keys_nodup firstMem secondMem)
    (Prod.ext familyEq sourceEq)

end P93CanonicalProgramGeneralComplete
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P93CanonicalProgramGeneralComplete.amboPayload_valid
assert_kernel_only TetraStereo.OneCenter.P93CanonicalProgramGeneralComplete.coveredClauses_exact
assert_kernel_only TetraStereo.OneCenter.P93CanonicalProgramGeneralComplete.entries_family_source_unique
