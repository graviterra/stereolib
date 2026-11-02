import TetraStereo.OneCenter.IUPACP93CanonicalSourceClaims

set_option autoImplicit false

/-!
# Provenance-bearing canonical P-93.1 examples

This module transcribes the four P-93.1 examples whose complete descriptor data are printed in
the frozen P-9 text.  The `ambo` row is intentionally absent because the exact full tocopherol
constitution printed in P-93.1.4 has not yet been transcribed into this source program.

Every source below is the complete heavy-atom constitutional graph of the printed compound.
Hydrogen atoms are implicit, as in the source names and ordinary molecular graph notation.
-/

namespace TetraStereo.OneCenter

open BlueBookP93
open IUPACNormativeProvision

namespace P93CanonicalProgramGeneral

def carbon : PeriodicElement where
  atomicNumber := 6
  positive := by decide
  atMost118 := by decide

def nitrogen : PeriodicElement where
  atomicNumber := 7
  positive := by decide
  atMost118 := by decide

def oxygen : PeriodicElement where
  atomicNumber := 8
  positive := by decide
  atMost118 := by decide

def chlorine : PeriodicElement where
  atomicNumber := 17
  positive := by decide
  atMost118 := by decide

def bromine : PeriodicElement where
  atomicNumber := 35
  positive := by decide
  atMost118 := by decide

def carbonAtom : SemanticAtom where element := carbon
def nitrogenAtom : SemanticAtom where element := nitrogen
def oxygenAtom : SemanticAtom where element := oxygen
def chlorineAtom : SemanticAtom where element := chlorine
def bromineAtom : SemanticAtom where element := bromine

def nitroNitrogenAtom : SemanticAtom where
  element := nitrogen
  formalCharge := 1

def nitroOxygenMinusAtom : SemanticAtom where
  element := oxygen
  formalCharge := -1

def bond (left right : Nat) (order : Nat := 1) : SemanticInteraction where
  participants := [left, right]
  kind := .covalent order

def citation (value : Nat) (primes : Nat := 0) : P93AuthorityCitationToken where
  components := [{ value := value, primes := primes }]

def assignment (center locant : Nat) (descriptor : BlueBookP93.Acyclic.Descriptor) :
    P93AuthorityLocatedAssignment P93CanonicalDescriptor where
  unit := .atomCenter center
  citation := citation locant
  descriptor := .acyclic descriptor

/-! ## P-93.1.1: `(2R)-butan-2-ol (PIN)` -/

/-- Full heavy-atom constitution: C1-C2(-O)-C3-C4. -/
def absoluteSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := [carbonAtom, carbonAtom, carbonAtom, carbonAtom, oxygenAtom]
      interactions := [bond 0 1, bond 1 2, bond 2 3, bond 1 4] }

theorem absoluteSource_structurallyWellFormed :
    absoluteSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    absoluteSource).mp (by decide)

theorem absoluteCenter_envelope :
    P93CanonicalPhysicalUnitEnvelope absoluteSource (.atomCenter 1) := by
  refine ⟨by decide, [0, 2, 4], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, absoluteSource, SemanticMolecule.atomCount]
  intro neighbor member
  simp at member
  rcases member with rfl | rfl | rfl <;> left <;>
    simp [P93AuthorityBinaryBond, absoluteSource, bond,
      P93AuthorityBinaryInteractionKind]

def absoluteConfiguration : P93CanonicalGeneralConfiguration where
  assignments := [assignment 1 2 .R]

def absolutePayload : P93GeneralClausePayload .absoluteConfiguration :=
  .absolute absoluteConfiguration

theorem absolutePayload_valid :
    (P93ClausePayloadData.general absolutePayload).ValidFor absoluteSource := by
  constructor
  · intro claim member
    simp [P93ClausePayloadData.toClaims, absolutePayload,
      P93GeneralClausePayload.toClaims, absoluteConfiguration,
      P93CanonicalGeneralConfiguration.toClaims] at member
    rcases member with rfl | rfl
    · exact ⟨by simp [assignment, citation, P93AuthorityCitationToken.Valid],
        absoluteCenter_envelope⟩
    · exact absoluteCenter_envelope
  · simp [absolutePayload, P93GeneralClausePayload.Intrinsic,
      P93CanonicalGeneralConfiguration.StructurallyComplete,
      absoluteConfiguration, assignment, citation]

def absoluteObservation :
    P93ClauseObservation absoluteSource (.general .absoluteConfiguration) where
  payload := .general absolutePayload
  validFor := absolutePayload_valid

def absoluteTranscription : P93CanonicalSourceTranscription absoluteSource
    (.general .absoluteConfiguration) absoluteObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 :=
    "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 36
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.1.1"
  clauseSectionExact := rfl
  observationSubsection := "P-93.1.1"
  observationSubsectionNonempty := by decide
  printedObservation := "(2R)-butan-2-ol (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _claimMember
    exact
      { supportingLocator := "PDF page 36, P-93.1.1, first named example and adjacent structure"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "(2R)-butan-2-ol (PIN); adjacent structure labels C-2 as R"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

/-! ## P-93.1.2.1: `rel-(2R,3R)-3-bromobutan-2-ol (PIN)` -/

/-- Full heavy-atom constitution: C1-C2(-O)-C3(-Br)-C4. -/
def relativeSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := [carbonAtom, carbonAtom, carbonAtom, carbonAtom, oxygenAtom, bromineAtom]
      interactions := [bond 0 1, bond 1 2, bond 2 3, bond 1 4, bond 2 5] }

theorem relativeSource_structurallyWellFormed :
    relativeSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    relativeSource).mp (by decide)

theorem relativeCenter2_envelope :
    P93CanonicalPhysicalUnitEnvelope relativeSource (.atomCenter 1) := by
  refine ⟨by decide, [0, 2, 4], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, relativeSource, SemanticMolecule.atomCount]
  intro neighbor member
  simp at member
  rcases member with rfl | rfl | rfl <;> left <;>
    simp [P93AuthorityBinaryBond, relativeSource, bond,
      P93AuthorityBinaryInteractionKind]

theorem relativeCenter3_envelope :
    P93CanonicalPhysicalUnitEnvelope relativeSource (.atomCenter 2) := by
  refine ⟨by decide, [1, 3, 5], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, relativeSource, SemanticMolecule.atomCount]
  intro neighbor member
  simp at member
  rcases member with rfl | rfl | rfl <;> left <;>
    simp [P93AuthorityBinaryBond, relativeSource, bond,
      P93AuthorityBinaryInteractionKind]

def relativeFirst : P93CanonicalGeneralConfiguration where
  assignments := [assignment 1 2 .R, assignment 2 3 .R]

def relativeSecond : P93CanonicalGeneralConfiguration where
  assignments := [assignment 1 2 .S, assignment 2 3 .S]

def relativeLeading : P93AuthorityLocatedAssignment P93CanonicalDescriptor :=
  assignment 1 2 .R

def relativePayload : P93GeneralClausePayload .relativeConfiguration :=
  .relative relativeFirst relativeSecond relativeLeading

theorem relativePayload_valid :
    (P93ClausePayloadData.general relativePayload).ValidFor relativeSource := by
  constructor
  · intro claim member
    simp [P93ClausePayloadData.toClaims, relativePayload,
      P93GeneralClausePayload.toClaims, relativeFirst, relativeSecond,
      P93CanonicalGeneralConfiguration.toClaims] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by simp [assignment, citation, P93AuthorityCitationToken.Valid],
        relativeCenter2_envelope⟩
    · exact relativeCenter2_envelope
    · exact ⟨by simp [assignment, citation, P93AuthorityCitationToken.Valid],
        relativeCenter3_envelope⟩
    · exact relativeCenter3_envelope
    · exact ⟨by simp [assignment, citation, P93AuthorityCitationToken.Valid],
        relativeCenter2_envelope⟩
    · exact relativeCenter2_envelope
    · exact ⟨by simp [assignment, citation, P93AuthorityCitationToken.Valid],
        relativeCenter3_envelope⟩
    · exact relativeCenter3_envelope
    · simp [P93SourceClaim.SourceEnvelope, P93GeneralClaim.SourceEnvelope,
        relativeLeading, assignment,
        P93CanonicalDescriptor.GeneralRepresentativeEligible,
        P93CanonicalDescriptor.mirror, P93CanonicalDescriptor.PreferredAtLowest]
  · simp [relativePayload, P93GeneralClausePayload.Intrinsic,
      P93CanonicalGeneralConfiguration.StructurallyComplete,
      P93CanonicalGeneralLeading, P93AuthorityConfiguration.RelativeEquivalent,
      P93AuthorityConfiguration.globallyMirrored, P93CanonicalDescriptor.mirrorAction,
      P93CanonicalDescriptor.mirror, P93CanonicalDescriptor.GeneralRepresentativeEligible,
      P93CanonicalDescriptor.PreferredAtLowest, relativeFirst, relativeSecond,
      relativeLeading, assignment, citation, P93AuthorityCitationToken.CitationLE,
      P93AuthorityCitationToken.key, P93AuthorityNatListLexLE]

def relativeObservation :
    P93ClauseObservation relativeSource (.general .relativeConfiguration) where
  payload := .general relativePayload
  validFor := relativePayload_valid

def relativeTranscription : P93CanonicalSourceTranscription relativeSource
    (.general .relativeConfiguration) relativeObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 :=
    "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 36
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.1.2.1"
  clauseSectionExact := rfl
  observationSubsection := "P-93.1.2.1"
  observationSubsectionNonempty := by decide
  printedObservation := "rel-(2R,3R)-3-bromobutan-2-ol (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _claimMember
    exact
      { supportingLocator :=
          "PDF page 36, P-93.1.2.1, second named example, adjacent structure, and 'or enantiomer'"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "rel-(2R,3R)-3-bromobutan-2-ol (PIN); (2R*,3R*)-3-bromobutan-2-ol; adjacent structure: or enantiomer"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

/-! ## P-93.1.2.2: mixed absolute and relative configuration -/

/--
Full heavy-atom constitution of
`1-{[(2S)-butan-2-yl]oxy}-3-chloro-5-nitrocyclohexane`:

* 0-5 are the cyclohexane ring C1-C6;
* 6 is ether O; 7-10 are the butan-2-yl carbons C2, C1, C3, C4;
* 11 is Cl; 12-14 are the nitro N and two O atoms.
-/
def mixedSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms :=
        [ carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom
        , oxygenAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom
        , chlorineAtom, nitroNitrogenAtom, oxygenAtom, nitroOxygenMinusAtom ]
      interactions :=
        [ bond 0 1, bond 1 2, bond 2 3, bond 3 4, bond 4 5, bond 5 0
        , bond 0 6, bond 6 7, bond 7 8, bond 7 9, bond 9 10
        , bond 2 11, bond 4 12, bond 12 13 2, bond 12 14 ] }

theorem mixedSource_structurallyWellFormed : mixedSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    mixedSource).mp (by decide)

theorem mixedCenter1_envelope :
    P93CanonicalPhysicalUnitEnvelope mixedSource (.atomCenter 0) := by
  refine ⟨by decide, [1, 5, 6], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, mixedSource, SemanticMolecule.atomCount]
  intro neighbor member
  simp at member
  rcases member with rfl | rfl | rfl <;> left <;>
    simp [P93AuthorityBinaryBond, mixedSource, bond,
      P93AuthorityBinaryInteractionKind]

theorem mixedCenter3_envelope :
    P93CanonicalPhysicalUnitEnvelope mixedSource (.atomCenter 2) := by
  refine ⟨by decide, [1, 3, 11], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, mixedSource, SemanticMolecule.atomCount]
  intro neighbor member
  simp at member
  rcases member with rfl | rfl | rfl <;> left <;>
    simp [P93AuthorityBinaryBond, mixedSource, bond,
      P93AuthorityBinaryInteractionKind]

theorem mixedCenter5_envelope :
    P93CanonicalPhysicalUnitEnvelope mixedSource (.atomCenter 4) := by
  refine ⟨by decide, [3, 5, 12], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, mixedSource, SemanticMolecule.atomCount]
  intro neighbor member
  simp at member
  rcases member with rfl | rfl | rfl <;> left <;>
    simp [P93AuthorityBinaryBond, mixedSource, bond,
      P93AuthorityBinaryInteractionKind]

theorem mixedSidechainCenter2_envelope :
    P93CanonicalPhysicalUnitEnvelope mixedSource (.atomCenter 7) := by
  refine ⟨by decide, [6, 8, 9], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, mixedSource, SemanticMolecule.atomCount]
  intro neighbor member
  simp at member
  rcases member with rfl | rfl | rfl <;> left <;>
    simp [P93AuthorityBinaryBond, mixedSource, bond,
      P93AuthorityBinaryInteractionKind]

def mixedConfiguration : P93CanonicalGeneralConfiguration where
  assignments :=
    [ assignment 0 1 .R
    , assignment 2 3 .R
    , assignment 4 5 .S
    , assignment 7 2 .S ]

def mixedPlan : P93CanonicalGeneralScopePlan where
  assignments :=
    [ ⟨assignment 0 1 .R, .relative 0⟩
    , ⟨assignment 2 3 .R, .relative 0⟩
    , ⟨assignment 4 5 .S, .relative 0⟩
    , ⟨assignment 7 2 .S, .absolute⟩ ]

def mixedTypography : List
    (P93AuthorityCitationToken × GeneralConfiguration.DescriptorTypography) :=
  [ (citation 1, .starred)
  , (citation 3, .starred)
  , (citation 5, .starred)
  , (citation 2, .plain) ]

def mixedPayload : P93GeneralClausePayload .mixedAbsoluteRelativeConfiguration :=
  .mixed mixedConfiguration mixedPlan mixedTypography

theorem mixedPayload_valid :
    (P93ClausePayloadData.general mixedPayload).ValidFor mixedSource := by
  constructor
  · intro claim member
    simp [P93ClausePayloadData.toClaims, mixedPayload,
      P93GeneralClausePayload.toClaims, mixedConfiguration,
      P93CanonicalGeneralConfiguration.toClaims] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by simp [assignment, citation, P93AuthorityCitationToken.Valid],
        mixedCenter1_envelope⟩
    · exact mixedCenter1_envelope
    · exact ⟨by simp [assignment, citation, P93AuthorityCitationToken.Valid],
        mixedCenter3_envelope⟩
    · exact mixedCenter3_envelope
    · exact ⟨by simp [assignment, citation, P93AuthorityCitationToken.Valid],
        mixedCenter5_envelope⟩
    · exact mixedCenter5_envelope
    · exact ⟨by simp [assignment, citation, P93AuthorityCitationToken.Valid],
        mixedSidechainCenter2_envelope⟩
    · exact mixedSidechainCenter2_envelope
  · simp [mixedPayload, P93GeneralClausePayload.Intrinsic,
      P93CanonicalGeneralConfiguration.StructurallyComplete,
      P93CanonicalMixedRelativeGroupsNontrivial, mixedConfiguration,
      mixedPlan, mixedTypography, assignment, citation,
      P93CanonicalDescriptor.GeneralRepresentativeEligible,
      P93CanonicalDescriptor.mirror]

def mixedObservation :
    P93ClauseObservation mixedSource (.general .mixedAbsoluteRelativeConfiguration) where
  payload := .general mixedPayload
  validFor := mixedPayload_valid

def mixedTranscription : P93CanonicalSourceTranscription mixedSource
    (.general .mixedAbsoluteRelativeConfiguration) mixedObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 :=
    "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 37
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.1.2.2"
  clauseSectionExact := rfl
  observationSubsection := "P-93.1.2.2"
  observationSubsectionNonempty := by decide
  printedObservation :=
    "(1R*,3R*,5S*)-1-{[(2S)-butan-2-yl]oxy}-3-chloro-5-nitrocyclohexane (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _claimMember
    exact
      { supportingLocator := "PDF page 37, P-93.1.2.2, sole named example and two adjacent structures"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "Printed PIN; figure labels 2S absolute and 1R*,3R*,5S* relative"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

/-! ## P-93.1.3: `rac-(2R)-2-bromobutane (PIN)` -/

/-- Full heavy-atom constitution: C1-C2(-Br)-C3-C4. -/
def racemateSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := [carbonAtom, carbonAtom, carbonAtom, carbonAtom, bromineAtom]
      interactions := [bond 0 1, bond 1 2, bond 2 3, bond 1 4] }

theorem racemateSource_structurallyWellFormed :
    racemateSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    racemateSource).mp (by decide)

theorem racemateCenter_envelope :
    P93CanonicalPhysicalUnitEnvelope racemateSource (.atomCenter 1) := by
  refine ⟨by decide, [0, 2, 4], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, racemateSource, SemanticMolecule.atomCount]
  intro neighbor member
  simp at member
  rcases member with rfl | rfl | rfl <;> left <;>
    simp [P93AuthorityBinaryBond, racemateSource, bond,
      P93AuthorityBinaryInteractionKind]

def racemateFirst : P93CanonicalGeneralConfiguration where
  assignments := [assignment 1 2 .R]

def racemateSecond : P93CanonicalGeneralConfiguration where
  assignments := [assignment 1 2 .S]

def racemateMixture : GeneralConfiguration.BinaryMixture P93CanonicalGeneralConfiguration where
  first := racemateFirst
  second := racemateSecond
  firstFraction := (1 : ℚ) / 2

def racemateLeading : P93AuthorityLocatedAssignment P93CanonicalDescriptor :=
  assignment 1 2 .R

def racematePayload : P93GeneralClausePayload .racemates :=
  .racemate racemateMixture racemateLeading

theorem racematePayload_valid :
    (P93ClausePayloadData.general racematePayload).ValidFor racemateSource := by
  constructor
  · intro claim member
    simp [P93ClausePayloadData.toClaims, racematePayload,
      P93GeneralClausePayload.toClaims, racemateMixture, racemateFirst,
      racemateSecond, P93CanonicalGeneralConfiguration.toClaims] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by simp [assignment, citation, P93AuthorityCitationToken.Valid],
        racemateCenter_envelope⟩
    · exact racemateCenter_envelope
    · exact ⟨by simp [assignment, citation, P93AuthorityCitationToken.Valid],
        racemateCenter_envelope⟩
    · exact racemateCenter_envelope
    · simp [P93SourceClaim.SourceEnvelope, P93GeneralClaim.SourceEnvelope,
        racemateLeading, assignment,
        P93CanonicalDescriptor.GeneralRepresentativeEligible,
        P93CanonicalDescriptor.mirror, P93CanonicalDescriptor.PreferredAtLowest]
  · simp [racematePayload, P93GeneralClausePayload.Intrinsic,
      P93CanonicalGeneralConfiguration.StructurallyComplete,
      P93CanonicalGeneralLeading, GeneralConfiguration.BinaryMixture.Valid,
      P93AuthorityConfiguration.globallyMirrored, P93CanonicalDescriptor.mirrorAction,
      P93CanonicalDescriptor.mirror, P93CanonicalDescriptor.GeneralRepresentativeEligible,
      P93CanonicalDescriptor.PreferredAtLowest, racemateMixture, racemateFirst,
      racemateSecond, racemateLeading, assignment, citation,
      P93AuthorityCitationToken.CitationLE, P93AuthorityCitationToken.key,
      P93AuthorityNatListLexLE]; norm_num

def racemateObservation :
    P93ClauseObservation racemateSource (.general .racemates) where
  payload := .general racematePayload
  validFor := racematePayload_valid

def racemateTranscription : P93CanonicalSourceTranscription racemateSource
    (.general .racemates) racemateObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 :=
    "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 37
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.1.3"
  clauseSectionExact := rfl
  observationSubsection := "P-93.1.3"
  observationSubsectionNonempty := by decide
  printedObservation := "rac-(2R)-2-bromobutane (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _claimMember
    exact
      { supportingLocator :=
          "PDF page 37, P-93.1.3, third named example, adjacent structure, and 'and enantiomer'"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "Equimolecular pair; printed rac-(2R) PIN and (2RS) alternative; and enantiomer"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

/-! ## Entries and exact four-clause coverage -/

def absoluteEntry : P93CanonicalClauseObservationEntry where
  source := absoluteSource
  sourceAdmitted := absoluteSource_structurallyWellFormed
  clause := .general .absoluteConfiguration
  clauseListed := by
    simp [P93Clause.all, Remaining71P93ClosedProductionRow.all,
      Remaining71P93ClosedProductionRow.generalRows,
      Remaining71P93GeneralAuthorityRow.all]
  observation := absoluteObservation
  transcription := absoluteTranscription

def relativeEntry : P93CanonicalClauseObservationEntry where
  source := relativeSource
  sourceAdmitted := relativeSource_structurallyWellFormed
  clause := .general .relativeConfiguration
  clauseListed := by
    simp [P93Clause.all, Remaining71P93ClosedProductionRow.all,
      Remaining71P93ClosedProductionRow.generalRows,
      Remaining71P93GeneralAuthorityRow.all]
  observation := relativeObservation
  transcription := relativeTranscription

def mixedEntry : P93CanonicalClauseObservationEntry where
  source := mixedSource
  sourceAdmitted := mixedSource_structurallyWellFormed
  clause := .general .mixedAbsoluteRelativeConfiguration
  clauseListed := by
    simp [P93Clause.all, Remaining71P93ClosedProductionRow.all,
      Remaining71P93ClosedProductionRow.generalRows,
      Remaining71P93GeneralAuthorityRow.all]
  observation := mixedObservation
  transcription := mixedTranscription

def racemateEntry : P93CanonicalClauseObservationEntry where
  source := racemateSource
  sourceAdmitted := racemateSource_structurallyWellFormed
  clause := .general .racemates
  clauseListed := by
    simp [P93Clause.all, Remaining71P93ClosedProductionRow.all,
      Remaining71P93ClosedProductionRow.generalRows,
      Remaining71P93GeneralAuthorityRow.all]
  observation := racemateObservation
  transcription := racemateTranscription

def entries : List P93CanonicalClauseObservationEntry :=
  [absoluteEntry, relativeEntry, mixedEntry, racemateEntry]

def coveredClauses : List P93Clause :=
  [ .general .absoluteConfiguration
  , .general .relativeConfiguration
  , .general .mixedAbsoluteRelativeConfiguration
  , .general .racemates ]

def canonicalCoveredClauses : List P93Clause :=
  (Remaining71P93GeneralAuthorityRow.all.filter fun row => row != .ambo).map .general

@[simp] theorem entries_length : entries.length = 4 := rfl

@[simp] theorem entries_clause_exact : entries.map (fun entry => entry.clause) = coveredClauses :=
  rfl

theorem coveredClauses_canonical_exact : coveredClauses = canonicalCoveredClauses := by
  rfl

theorem coveredClauses_nodup : coveredClauses.Nodup := by
  decide

theorem entry_sources_pairwise_distinct :
    (entries.map fun entry => entry.source).Nodup := by
  decide

theorem entries_source_unique :
    ∀ first ∈ entries, ∀ second ∈ entries,
      first.source = second.source → first = second := by
  intro first firstMember second secondMember sourceEq
  simp [entries] at firstMember secondMember
  rcases firstMember with rfl | rfl | rfl | rfl <;>
    rcases secondMember with rfl | rfl | rfl | rfl
  all_goals try rfl
  all_goals exfalso
  all_goals exact (by decide : _ ≠ _) sourceEq

theorem coveredClause_has_entry (clause : P93Clause) (member : clause ∈ coveredClauses) :
    ∃ entry ∈ entries, entry.clause = clause := by
  simp [coveredClauses] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨absoluteEntry, by simp [entries], rfl⟩
  · exact ⟨relativeEntry, by simp [entries], rfl⟩
  · exact ⟨mixedEntry, by simp [entries], rfl⟩
  · exact ⟨racemateEntry, by simp [entries], rfl⟩

end P93CanonicalProgramGeneral
end TetraStereo.OneCenter
