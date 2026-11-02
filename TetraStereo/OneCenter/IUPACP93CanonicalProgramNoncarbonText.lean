import TetraStereo.OneCenter.IUPACP93CanonicalSourceClaims

set_option autoImplicit false
set_option maxRecDepth 4096

/-!
# Verified textual P-93.2 noncarbon examples

This module transcribes four distinct examples from the frozen Blue Book P-9 artifact.  The
constitutional graphs contain every named heavy atom, including the bromide counterions in the
two onium salts.  Descriptor handedness is transcribed from the printed PIN and is not inferred
from the graph.
-/

namespace TetraStereo.OneCenter

open BlueBookP93
open BlueBookP93.NoncarbonTetrahedra
open IUPACNormativeProvision

namespace P93CanonicalProgramNoncarbonText

def nitrogen : PeriodicElement where
  atomicNumber := 7
  positive := by decide
  atMost118 := by decide

def oxygen : PeriodicElement where
  atomicNumber := 8
  positive := by decide
  atMost118 := by decide

def phosphorus : PeriodicElement where
  atomicNumber := 15
  positive := by decide
  atMost118 := by decide

def bromine : PeriodicElement where
  atomicNumber := 35
  positive := by decide
  atMost118 := by decide

def carbon : PeriodicElement where
  atomicNumber := 6
  positive := by decide
  atMost118 := by decide

def atom (element : PeriodicElement) (formalCharge : Int := 0) : SemanticAtom where
  element := element
  formalCharge := formalCharge

def bond (left right order : Nat) : SemanticInteraction where
  participants := [left, right]
  kind := .covalent order

theorem assignmentBaseClaims_valid
    {source : AuthoritativeChemicalInput} (assignment : P93NoncarbonAssignmentPayload)
    (valid : assignment.frame.StructurallyValidFor source) :
    ∀ claim ∈ assignment.baseClaims, claim.SourceEnvelope source := by
  rcases valid with ⟨bounded, lengthExact, nodup, incidence, noncarbon⟩
  intro claim claimMember
  simp [P93NoncarbonAssignmentPayload.baseClaims] at claimMember
  rcases claimMember with rfl | rfl
  · refine ⟨bounded assignment.frame.center (by simp), ?_, nodup, ?_⟩
    · omega
    · intro ligand ligandMember
      exact bounded ligand (by simp [ligandMember])
  · refine ⟨bounded assignment.frame.center (by simp), assignment.frame.ligands, ?_,
      nodup, ?_, ?_⟩
    · omega
    · intro ligand ligandMember
      exact bounded ligand (by simp [ligandMember])
    · intro ligand ligandMember
      exact (incidence ligand).2 ligandMember

/-! ## P-93.2 / P-93.2.3: noncarbon tetrahedron -/

/-- Full heavy-atom graph of methyl(phenyl)(propyl)-lambda5-phosphanone: P=O, methyl,
propyl, and phenyl are all represented. -/
def phosphanoneSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms :=
        [ atom phosphorus, atom oxygen, atom carbon, atom carbon, atom carbon, atom carbon
        , atom carbon, atom carbon, atom carbon, atom carbon, atom carbon, atom carbon ]
      interactions :=
        [ bond 0 1 2, bond 0 2 1, bond 0 3 1, bond 0 6 1
        , bond 3 4 1, bond 4 5 1
        , bond 6 7 2, bond 7 8 1, bond 8 9 2
        , bond 9 10 1, bond 10 11 2, bond 11 6 1 ] }

def phosphanoneAssignment : P93NoncarbonAssignmentPayload where
  frame := { center := 0, ligands := [1, 2, 3, 6] }
  descriptor := .acyclic .S

theorem phosphanoneSource_structurallyWellFormed :
    phosphanoneSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    phosphanoneSource).mp (by decide)

theorem phosphanoneFrame_valid :
    phosphanoneAssignment.frame.StructurallyValidFor phosphanoneSource := by
  simp [P93NoncarbonTetrahedralFrame.StructurallyValidFor, phosphanoneAssignment,
    phosphanoneSource, P93AuthorityAtomsBounded, P93AuthorityBinaryBond,
    P93AuthorityMulticenterIncidence, P93AuthorityBinaryInteractionKind, bond,
    SemanticMolecule.atomCount, atom, phosphorus]
  intro ligand
  omega

def phosphanonePayload : P93NoncarbonClausePayload .otherElementTetrahedra :=
  .tetrahedra phosphanoneAssignment

theorem phosphanonePayload_valid :
    (P93ClausePayloadData.noncarbon phosphanonePayload).ValidFor phosphanoneSource := by
  refine ⟨?_, phosphanoneFrame_valid⟩
  exact assignmentBaseClaims_valid phosphanoneAssignment phosphanoneFrame_valid

def phosphanoneObservation : P93ClauseObservation phosphanoneSource
    (.noncarbon .otherElementTetrahedra) where
  payload := .noncarbon phosphanonePayload
  validFor := phosphanonePayload_valid

/-! ## P-93.2.1/.2: numerical methodology example -/

/-- Full heavy-atom graph of
2-(4-hydroxyphenyl)-2-phenyl-1,2,3,4-tetrahydroisophosphinolin-2-ium bromide.
Atoms 1 and 2 are the two saturated ring neighbors of P; atoms 3 and 4 complete the saturated
side up to the lower fusion atom, atoms 4--9 are the fused benzene, 10--15 the
4-hydroxyphenyl group, 17--22 the phenyl group, and 23 is bromide. -/
def methodologySource : AuthoritativeChemicalInput where
  molecule :=
    { atoms :=
        [ atom phosphorus 1
        , atom carbon, atom carbon, atom carbon, atom carbon, atom carbon, atom carbon
        , atom carbon, atom carbon
        , atom carbon, atom carbon, atom carbon, atom carbon, atom carbon, atom carbon
        , atom carbon, atom oxygen
        , atom carbon, atom carbon, atom carbon, atom carbon, atom carbon, atom carbon
        , atom bromine (-1) ]
      interactions :=
        [ bond 0 1 1, bond 0 2 1, bond 0 10 1, bond 0 17 1
        , bond 1 9 1, bond 2 3 1, bond 3 4 1
        , bond 4 5 2, bond 5 6 1, bond 6 7 2
        , bond 7 8 1, bond 8 9 2, bond 9 4 1
        , bond 10 11 2, bond 11 12 1, bond 12 13 2
        , bond 13 14 1, bond 14 15 2, bond 15 10 1, bond 13 16 1
        , bond 17 18 2, bond 18 19 1, bond 19 20 2
        , bond 20 21 1, bond 21 22 2, bond 22 17 1 ] }

def methodologyAssignment : P93NoncarbonAssignmentPayload where
  frame := { center := 0, ligands := [1, 2, 10, 17] }
  descriptor := .acyclic .S

def methodologyCitation : P93AuthorityCitationToken where
  components := [{ value := 2 }]

def methodologyRule : DescriptorCitationObservation where
  context := .preferredIUPACName
  centralElement := .phosphorus
  locant := .numerical
  compoundNameNested := false

theorem methodologySource_structurallyWellFormed :
    methodologySource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    methodologySource).mp (by decide)

theorem methodologyFrame_valid :
    methodologyAssignment.frame.StructurallyValidFor methodologySource := by
  simp [P93NoncarbonTetrahedralFrame.StructurallyValidFor, methodologyAssignment,
    methodologySource, P93AuthorityAtomsBounded, P93AuthorityBinaryBond,
    P93AuthorityMulticenterIncidence, P93AuthorityBinaryInteractionKind, bond,
    SemanticMolecule.atomCount, atom, phosphorus]
  intro ligand
  omega

def methodologyPayload : P93NoncarbonClausePayload .otherElementGeneralMethodology :=
  .methodology methodologyAssignment (some methodologyCitation) methodologyRule

theorem methodologyPayload_valid :
    (P93ClausePayloadData.noncarbon methodologyPayload).ValidFor methodologySource := by
  refine ⟨?_, methodologyFrame_valid, ?_, ?_, ?_⟩
  · intro claim claimMember
    change claim ∈ methodologyAssignment.baseClaims ++
      [.noncarbon (.citation methodologyCitation (.atomCenter 0))] at claimMember
    rw [List.mem_append] at claimMember
    rcases claimMember with baseMember | citationMember
    · exact assignmentBaseClaims_valid methodologyAssignment methodologyFrame_valid
        claim baseMember
    · have claimExact : claim =
          .noncarbon (.citation methodologyCitation (.atomCenter 0)) := by
        simpa using citationMember
      subst claim
      refine ⟨by simp [P93AuthorityCitationToken.Valid, methodologyCitation], ?_⟩
      exact (assignmentBaseClaims_valid methodologyAssignment methodologyFrame_valid)
        (.noncarbon (.descriptor (.atomCenter 0) (.acyclic .S)))
          (by simp [P93NoncarbonAssignmentPayload.baseClaims, methodologyAssignment])
  · exact ⟨atom phosphorus 1, by simp [methodologyAssignment, methodologySource], rfl⟩
  · exact ⟨methodologyCitation, rfl, by simp [P93AuthorityCitationToken.Valid,
      methodologyCitation]⟩
  · simp [CitationConforms, methodologyRule]

def methodologyObservation : P93ClauseObservation methodologySource
    (.noncarbon .otherElementGeneralMethodology) where
  payload := .noncarbon methodologyPayload
  validFor := methodologyPayload_valid

/-! ## P-93.2.2: azanium -/

/-- Full heavy-atom graph of N-benzyl-N-methyl-N-(prop-2-en-1-yl)anilinium bromide.
The two phenyl rings, benzyl methylene, complete allyl group, methyl group, and bromide are retained. -/
def azaniumSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms :=
        [ atom nitrogen 1, atom carbon
        , atom carbon, atom carbon, atom carbon, atom carbon, atom carbon, atom carbon
        , atom carbon
        , atom carbon, atom carbon, atom carbon, atom carbon, atom carbon, atom carbon
        , atom carbon, atom carbon, atom carbon
        , atom bromine (-1) ]
      interactions :=
        [ bond 0 1 1, bond 0 2 1, bond 0 8 1, bond 0 15 1
        , bond 2 3 2, bond 3 4 1, bond 4 5 2, bond 5 6 1, bond 6 7 2, bond 7 2 1
        , bond 8 9 1
        , bond 9 10 2, bond 10 11 1, bond 11 12 2
        , bond 12 13 1, bond 13 14 2, bond 14 9 1
        , bond 15 16 1, bond 16 17 2 ] }

def azaniumAssignment : P93NoncarbonAssignmentPayload where
  frame := { center := 0, ligands := [1, 2, 8, 15] }
  descriptor := .acyclic .R

theorem azaniumSource_structurallyWellFormed : azaniumSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff azaniumSource).mp
    (by decide)

theorem azaniumFrame_valid :
    azaniumAssignment.frame.StructurallyValidFor azaniumSource := by
  simp [P93NoncarbonTetrahedralFrame.StructurallyValidFor, azaniumAssignment,
    azaniumSource, P93AuthorityAtomsBounded, P93AuthorityBinaryBond,
    P93AuthorityMulticenterIncidence, P93AuthorityBinaryInteractionKind, bond,
    SemanticMolecule.atomCount, atom, nitrogen]
  intro ligand
  omega

def azaniumPayload : P93NoncarbonClausePayload .azaniumPhosphanium :=
  .onic azaniumAssignment .azanium

theorem azaniumPayload_valid :
    (P93ClausePayloadData.noncarbon azaniumPayload).ValidFor azaniumSource := by
  refine ⟨assignmentBaseClaims_valid azaniumAssignment azaniumFrame_valid,
    azaniumFrame_valid, ?_⟩
  exact ⟨atom nitrogen 1, by simp [azaniumAssignment, azaniumSource], rfl⟩

def azaniumObservation : P93ClauseObservation azaniumSource
    (.noncarbon .azaniumPhosphanium) where
  payload := .noncarbon azaniumPayload
  validFor := azaniumPayload_valid

/-! ## P-93.2.3: amine oxide -/

/-- Full charge-separated heavy-atom graph of N-ethyl-N-methylaniline N-oxide. -/
def oxideSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms :=
        [ atom nitrogen 1, atom oxygen (-1), atom carbon, atom carbon, atom carbon
        , atom carbon, atom carbon, atom carbon, atom carbon, atom carbon, atom carbon ]
      interactions :=
        [ bond 0 1 1, bond 0 2 1, bond 0 3 1, bond 0 5 1, bond 3 4 1
        , bond 5 6 2, bond 6 7 1, bond 7 8 2
        , bond 8 9 1, bond 9 10 2, bond 10 5 1 ] }

def oxideAssignment : P93NoncarbonAssignmentPayload where
  frame := { center := 0, ligands := [1, 2, 3, 5] }
  descriptor := .acyclic .S

theorem oxideSource_structurallyWellFormed : oxideSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff oxideSource).mp
    (by decide)

theorem oxideFrame_valid : oxideAssignment.frame.StructurallyValidFor oxideSource := by
  simp [P93NoncarbonTetrahedralFrame.StructurallyValidFor, oxideAssignment,
    oxideSource, P93AuthorityAtomsBounded, P93AuthorityBinaryBond,
    P93AuthorityMulticenterIncidence, P93AuthorityBinaryInteractionKind, bond,
    SemanticMolecule.atomCount, atom, nitrogen]
  intro ligand
  omega

def oxidePayload : P93NoncarbonClausePayload .aminePhosphaneOxides :=
  .oxide oxideAssignment 1 .amineOxide .chargeSeparatedSingle .writtenDouble

theorem oxidePayload_valid :
    (P93ClausePayloadData.noncarbon oxidePayload).ValidFor oxideSource := by
  refine ⟨?_, oxideFrame_valid, ?_, by simp [oxideAssignment], ?_, ?_, ?_, rfl⟩
  · intro claim claimMember
    change claim ∈ oxideAssignment.baseClaims ++
      [ .noncarbon (.oxideVariant 0 1 .amineOxide .chargeSeparatedSingle)
      , .noncarbon (.oxideVariant 0 1 .amineOxide .writtenDouble) ] at claimMember
    rw [List.mem_append] at claimMember
    rcases claimMember with baseMember | variantMember
    · exact assignmentBaseClaims_valid oxideAssignment oxideFrame_valid claim baseMember
    · simp at variantMember
      rcases variantMember with firstVariant | secondVariant
      · subst claim
        simp [P93SourceClaim.SourceEnvelope, P93NoncarbonClaim.SourceEnvelope, oxideSource,
          P93AuthorityBinaryBond,
          P93AuthorityBinaryInteractionKind, bond, SemanticMolecule.atomCount]
      · subst claim
        simp [P93SourceClaim.SourceEnvelope, P93NoncarbonClaim.SourceEnvelope, oxideSource,
          P93AuthorityBinaryBond,
          P93AuthorityBinaryInteractionKind, bond, SemanticMolecule.atomCount]
  · exact ⟨atom nitrogen 1, by simp [oxideAssignment, oxideSource], rfl⟩
  · exact ⟨atom oxygen (-1), by simp [oxideSource], rfl⟩
  · simp [oxideAssignment, P93AuthorityBinaryBond, oxideSource,
      P93AuthorityBinaryInteractionKind, bond]
  · decide

def oxideObservation : P93ClauseObservation oxideSource
    (.noncarbon .aminePhosphaneOxides) where
  payload := .noncarbon oxidePayload
  validFor := oxidePayload_valid

/-! ## Claim-complete frozen provenance -/

def blueBookP9Sha256 : String :=
  "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"

def phosphanoneTranscription : P93CanonicalSourceTranscription phosphanoneSource
    (.noncarbon .otherElementTetrahedra) phosphanoneObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := blueBookP9Sha256
  artifactSha256Exact := rfl
  pdfPage := 39
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.2"
  clauseSectionExact := rfl
  observationSubsection := "P-93.2.3"
  observationSubsectionNonempty := by decide
  printedObservation := "(S)-methyl(phenyl)(propyl)-λ5-phosphanone (PIN; see P-74.2.1.4)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro _claim _claimMember
    exact
      { supportingLocator :=
          "PDF page 38, P-93.2/P-93.2.3 rule text; PDF page 39, continuing named example and adjacent structure"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "The CIP priority system described for stereogenic carbon centers is extended to any atom having four ligands tetrahedrally arranged. (S)-methyl(phenyl)(propyl)-λ5-phosphanone (PIN; see P-74.2.1.4)."
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def methodologyTranscription : P93CanonicalSourceTranscription methodologySource
    (.noncarbon .otherElementGeneralMethodology) methodologyObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := blueBookP9Sha256
  artifactSha256Exact := rfl
  pdfPage := 38
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.2.1"
  clauseSectionExact := rfl
  observationSubsection := "P-93.2.1/P-93.2.2"
  observationSubsectionNonempty := by decide
  printedObservation :=
    "(2S)-2-(4-hydroxyphenyl)-2-phenyl-1,2,3,4-tetrahydroisophosphinolin-2-ium bromide (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro _claim _claimMember
    exact
      { supportingLocator := "PDF page 38, P-93.2.1 numerical-locant rule and P-93.2.2 second example/structure"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "Numerical locants are used before stereodescriptors, but letter locants such as N, O or S are not. (2S)-2-(4-hydroxyphenyl)-2-phenyl-1,2,3,4-tetrahydroisophosphinolin-2-ium bromide (PIN)."
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def azaniumTranscription : P93CanonicalSourceTranscription azaniumSource
    (.noncarbon .azaniumPhosphanium) azaniumObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := blueBookP9Sha256
  artifactSha256Exact := rfl
  pdfPage := 38
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.2.2"
  clauseSectionExact := rfl
  observationSubsection := "P-93.2.2"
  observationSubsectionNonempty := by decide
  printedObservation :=
    "(R)-N-benzyl-N-methyl-N-(prop-2-en-1-yl)anilinium bromide (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro _claim _claimMember
    exact
      { supportingLocator := "PDF page 38, P-93.2.2, four-ligand rule and first example/structure"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "The four different ligands are considered in priority order a > b > c > d in the manner described in P-92.2. (R)-N-benzyl-N-methyl-N-(prop-2-en-1-yl)anilinium bromide (PIN)."
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def oxideTranscription : P93CanonicalSourceTranscription oxideSource
    (.noncarbon .aminePhosphaneOxides) oxideObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := blueBookP9Sha256
  artifactSha256Exact := rfl
  pdfPage := 38
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.2.3"
  clauseSectionExact := rfl
  observationSubsection := "P-93.2.3"
  observationSubsectionNonempty := by decide
  printedObservation := "(S)-N-ethyl-N-methylaniline N-oxide (PIN; see P-74.2.1.2)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro _claim _claimMember
    exact
      { supportingLocator := "PDF page 38, P-93.2.3, rule text and first example/structure"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "With chiral amine oxides and phosphane oxides the oxygen atom is treated as the fourth atom. The nature of the bonding to this oxygen atom is not relevant. (S)-N-ethyl-N-methylaniline N-oxide (PIN; see P-74.2.1.2)."
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

/-! ## Entries, source-key uniqueness, and exact four-clause coverage -/

def phosphanoneEntry : P93CanonicalClauseObservationEntry where
  source := phosphanoneSource
  sourceAdmitted := phosphanoneSource_structurallyWellFormed
  clause := .noncarbon .otherElementTetrahedra
  clauseListed := by
    simp [P93Clause.all, Remaining71P93ClosedProductionRow.all,
      Remaining71P93ClosedProductionRow.noncarbonRows,
      Remaining71P93NoncarbonAuthorityRow.all]
  observation := phosphanoneObservation
  transcription := phosphanoneTranscription

def methodologyEntry : P93CanonicalClauseObservationEntry where
  source := methodologySource
  sourceAdmitted := methodologySource_structurallyWellFormed
  clause := .noncarbon .otherElementGeneralMethodology
  clauseListed := by
    simp [P93Clause.all, Remaining71P93ClosedProductionRow.all,
      Remaining71P93ClosedProductionRow.noncarbonRows,
      Remaining71P93NoncarbonAuthorityRow.all]
  observation := methodologyObservation
  transcription := methodologyTranscription

def azaniumEntry : P93CanonicalClauseObservationEntry where
  source := azaniumSource
  sourceAdmitted := azaniumSource_structurallyWellFormed
  clause := .noncarbon .azaniumPhosphanium
  clauseListed := by
    simp [P93Clause.all, Remaining71P93ClosedProductionRow.all,
      Remaining71P93ClosedProductionRow.noncarbonRows,
      Remaining71P93NoncarbonAuthorityRow.all]
  observation := azaniumObservation
  transcription := azaniumTranscription

def oxideEntry : P93CanonicalClauseObservationEntry where
  source := oxideSource
  sourceAdmitted := oxideSource_structurallyWellFormed
  clause := .noncarbon .aminePhosphaneOxides
  clauseListed := by
    simp [P93Clause.all, Remaining71P93ClosedProductionRow.all,
      Remaining71P93ClosedProductionRow.noncarbonRows,
      Remaining71P93NoncarbonAuthorityRow.all]
  observation := oxideObservation
  transcription := oxideTranscription

def entries : List P93CanonicalClauseObservationEntry :=
  [phosphanoneEntry, methodologyEntry, azaniumEntry, oxideEntry]

def coveredClauses : List P93Clause := entries.map fun entry => entry.clause

@[simp] theorem entries_length : entries.length = 4 := rfl

@[simp] theorem coveredClauses_exact : coveredClauses =
    [ .noncarbon .otherElementTetrahedra
    , .noncarbon .otherElementGeneralMethodology
    , .noncarbon .azaniumPhosphanium
    , .noncarbon .aminePhosphaneOxides ] := rfl

theorem coveredClauses_nodup : coveredClauses.Nodup := by decide

theorem covered_clause_has_entry (clause : P93Clause) (covered : clause ∈ coveredClauses) :
    ∃ entry ∈ entries, entry.clause = clause := by
  simpa [coveredClauses] using covered

theorem entries_source_unique :
    ∀ first ∈ entries, ∀ second ∈ entries,
      first.source = second.source → first = second := by
  intro first firstMember second secondMember sourceExact
  simp [entries] at firstMember secondMember
  rcases firstMember with rfl | rfl | rfl | rfl <;>
    rcases secondMember with rfl | rfl | rfl | rfl <;> try rfl
  all_goals
    exfalso
    have atomCountExact := congrArg (fun input => input.molecule.atomCount) sourceExact
    norm_num [phosphanoneEntry, methodologyEntry, azaniumEntry, oxideEntry,
      phosphanoneSource, methodologySource, azaniumSource, oxideSource,
      SemanticMolecule.atomCount] at atomCountExact

end P93CanonicalProgramNoncarbonText
end TetraStereo.OneCenter
