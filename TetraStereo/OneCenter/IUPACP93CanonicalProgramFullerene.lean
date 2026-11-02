import TetraStereo.OneCenter.IUPACP93CanonicalSourceClaims
import TetraStereo.OneCenter.IUPACP93CanonicalFullereneRelationalAuthorityObservations

set_option autoImplicit false
set_option maxRecDepth 4096

/-!
# Canonical P-93.5.6 fullerene program compiler

The six fullerene clauses reduce to one textual methodology entry and three independently
transcribed numbered cages: C76 for Type 1, C60 shared by Types 2 and 3, and C70 shared by Type 4
and the superimposed case.  No edge table is copied beside the facial rotation system.  The
canonical undirected edge table and the all-carbon cage core are executable projections of the
single oriented-face transcription.

The five printed derivatives remain honest source data.  Each supplies its complete raw molecule,
printed substituent inventory, executable observation, and exact agreement proofs.  In particular,
this compiler cannot turn a bare cage into a substituted example.  What it removes is duplicated
row assembly: once the three cage packages and five audited derivative records are supplied, all
six clause entries and their source-key invariants are generated together.
-/

namespace TetraStereo.OneCenter

open BlueBookP93
open BlueBookP93.Cyclic
open IUPACNormativeProvision

namespace P93CanonicalProgramFullerene

/-! ## Frozen methodology entry -/

def methodologySource : AuthoritativeChemicalInput where
  molecule := { atoms := [], interactions := [] }

theorem methodologySource_structurallyWellFormed : methodologySource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff methodologySource).mp
    (by decide)

def methodologyObservation :
    P93ClauseObservation methodologySource (.fullerene .generalMethodology) where
  payload := .fullerene .methodology
  validFor := by
    constructor
    · intro claim member
      simp only [P93ClausePayloadData.toClaims, P93FullereneClausePayload.toClaims] at member
      simp only [List.mem_singleton] at member
      subst claim
      exact p93FullereneFourWaySubstitutionDecisionRule
    · trivial

def frozenTranscription
    (source : AuthoritativeChemicalInput) (clause : P93Clause)
    (observation : P93ClauseObservation source clause)
    (pdfPage : Nat) (pdfPagePositive : 0 < pdfPage) (pdfPageWithin : pdfPage ≤ 91)
    (clauseSectionValue : String)
    (sectionExact : clauseSectionValue = clause.provision.sourceSection)
    (subsection printed locator : String)
    (subsectionNonempty : subsection ≠ "") (printedNonempty : printed ≠ "")
    (locatorNonempty : locator ≠ "") (mode : P93SourceObservationMode) :
    P93CanonicalSourceTranscription source clause observation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := pdfPage
  pdfPagePositive := pdfPagePositive
  pdfPageWithinFrozenArtifact := pdfPageWithin
  clauseSection := clauseSectionValue
  clauseSectionExact := sectionExact
  observationSubsection := subsection
  observationSubsectionNonempty := subsectionNonempty
  printedObservation := printed
  printedObservationNonempty := printedNonempty
  claimTranscriptions := by
    intro claim _
    exact
      { supportingLocator := locator
        supportingLocatorNonempty := locatorNonempty
        supportingObservation := printed
        supportingObservationNonempty := printedNonempty
        mode := mode }

def methodologyTranscription : P93CanonicalSourceTranscription methodologySource
    (.fullerene .generalMethodology) methodologyObservation :=
  frozenTranscription methodologySource (.fullerene .generalMethodology) methodologyObservation
    79 (by decide) (by decide) "P-93.5.6.1" rfl "Definitions and general methodology"
    "Four-way classification by the stepwise achiral test-substituent T substitution test."
    "PDF pages 79-80, P-93.5.6.1 and Fig. 9.2" (by decide) (by decide) (by decide)
    .verbatimText

def methodologyEntry : P93CanonicalClauseObservationEntry where
  source := methodologySource
  sourceAdmitted := methodologySource_structurallyWellFormed
  clause := .fullerene .generalMethodology
  clauseListed := by decide
  observation := methodologyObservation
  transcription := methodologyTranscription

/-! ## Five direct relational release entries -/

noncomputable section

/-- Exact clause identity for every audited relational release row. -/
def relationalClause (row : P93RelationalFullereneReleaseRow) : P93Clause :=
  match row with
  | .inherentParent => .fullerene .inherentParentChirality
  | .inherentSubstitution => .fullerene .inherentSubstitutionChirality
  | .noninherentSubstitution => .fullerene .noninherentSubstitutionChirality
  | .chiralSubstituents => .fullerene .chiralSubstituents
  | .superimposed => .fullerene .superimposedStereogenicElements

/-- Shared entry constructor for the five relational rows.  Its observation is already the
source-audited relational payload; no site-rooted compatibility carrier is reconstructed. -/
def relationalEntryOf
    (source : AuthoritativeChemicalInput) (sourceAdmitted : source.StructurallyWellFormed)
    (clause : P93Clause) (clauseListed : clause ∈ P93Clause.all)
    (observation : P93ClauseObservation source clause)
    (pdfPage : Nat) (pdfPagePositive : 0 < pdfPage) (pdfPageWithin : pdfPage ≤ 91)
    (clauseSectionValue : String)
    (sectionExact : clauseSectionValue = clause.provision.sourceSection)
    (subsection printed locator : String)
    (subsectionNonempty : subsection ≠ "") (printedNonempty : printed ≠ "")
    (locatorNonempty : locator ≠ "") : P93CanonicalClauseObservationEntry where
  source := source
  sourceAdmitted := sourceAdmitted
  clause := clause
  clauseListed := clauseListed
  observation := observation
  transcription := frozenTranscription source clause observation pdfPage pdfPagePositive
    pdfPageWithin clauseSectionValue sectionExact subsection printed locator
    subsectionNonempty printedNonempty locatorNonempty .textAndFigure

/-- Total source-program entry lookup.  Every branch consumes the public relational observation
and its public source-validity theorem directly. -/
def relationalEntry :
    P93RelationalFullereneReleaseRow → P93CanonicalClauseObservationEntry
  | .inherentParent =>
      relationalEntryOf
        iupacP93CanonicalFullereneC76Type1AuthoritySource
        iupacP93CanonicalFullereneAuthoritySources_all_structurallyWellFormed.1
        (.fullerene .inherentParentChirality) (by decide)
        { payload := .fullerene
            (.inherentParent iupacP93CanonicalFullereneC76Type1AuthorityObservation)
          validFor := by
            constructor
            · simp [P93ClausePayloadData.toClaims, P93FullereneClausePayload.toClaims]
            · exact ⟨iupacP93CanonicalFullereneC76Type1AuthorityObservation_valid, rfl⟩ }
        80 (by decide) (by decide) "P-93.5.6.2" rfl
        "Type 1. Inherently chiral parent fullerenes"
        "The printed (C76-D2)[5,6]fullerene enantiomer and its f,sA/f,sC systematic numbering."
        "PDF page 80, P-93.5.6.2, numbered C76-D2 diagrams"
        (by decide) (by decide) (by decide)
  | .inherentSubstitution =>
      relationalEntryOf
        iupacP93CanonicalFullereneC60Type2AuthoritySource
        iupacP93CanonicalFullereneAuthoritySources_all_structurallyWellFormed.2.1
        (.fullerene .inherentSubstitutionChirality) (by decide)
        { payload := .fullerene
            (.inherentSubstitution iupacP93CanonicalFullereneC60Type2AuthorityObservation)
          validFor := by
            constructor
            · simp [P93ClausePayloadData.toClaims, P93FullereneClausePayload.toClaims]
            · exact ⟨iupacP93CanonicalFullereneC60Type2AuthorityObservation_valid, rfl⟩ }
        81 (by decide) (by decide) "P-93.5.6.3" rfl
        "Type 2. Substituted fullerenes inherently chiral because of their substitution pattern"
        "(f,sC)-1,23-bis[1,1,1,3,3,3-hexamethyl-2-(trimethylsilyl)trisilan-2-yl]-1,23-dihydro(C60-Ih)[5,6]fullerene (PIN)"
        "PDF page 81, P-93.5.6.3, example and adjacent numbered C60 diagram"
        (by decide) (by decide) (by decide)
  | .noninherentSubstitution =>
      relationalEntryOf
        iupacP93CanonicalFullereneC60Type3AuthoritySource
        iupacP93CanonicalFullereneAuthoritySources_all_structurallyWellFormed.2.2.1
        (.fullerene .noninherentSubstitutionChirality) (by decide)
        { payload := .fullerene
            (.noninherentSubstitution iupacP93CanonicalFullereneC60Type3AuthorityObservation)
          validFor := by
            constructor
            · simp [P93ClausePayloadData.toClaims, P93FullereneClausePayload.toClaims]
            · exact ⟨iupacP93CanonicalFullereneC60Type3AuthorityObservation_valid, rfl⟩ }
        81 (by decide) (by decide) "P-93.5.6.4" rfl
        "Type 3. Substituted fullerenes noninherently chiral because of their substitution pattern"
        "1-tert-butyl-7-(3,6-dicyclopropylcyclohepta-2,4,6-trien-1-yl)-1,7-dihydro(C60-Ih)[5,6]fullerene (PIN)"
        "PDF page 81, P-93.5.6.4, example and paired enantiomer diagrams"
        (by decide) (by decide) (by decide)
  | .chiralSubstituents =>
      relationalEntryOf
        iupacP93CanonicalFullereneC70Type4AuthoritySource
        iupacP93CanonicalFullereneAuthoritySources_all_structurallyWellFormed.2.2.2.1
        (.fullerene .chiralSubstituents) (by decide)
        { payload := .fullerene
            (.chiralSubstituents iupacP93CanonicalFullereneC70Type4AuthorityObservation)
          validFor := by
            constructor
            · simp [P93ClausePayloadData.toClaims, P93FullereneClausePayload.toClaims]
            · exact iupacP93CanonicalFullereneC70Type4AuthorityObservation_valid }
        82 (by decide) (by decide) "P-93.5.6.5" rfl
        "Type 4. Chirality due to chiral substituents"
        "tetrakis[(1S)-1-phenylbutyl] 3′H,3′′H-dicyclopropa[8,25:16,35](C70-D5h(6))[5,6]fullerene-3′,3′,3′′,3′′-tetracarboxylate (PIN)"
        "PDF page 82, P-93.5.6.5, example and adjacent C70 derivative diagram"
        (by decide) (by decide) (by decide)
  | .superimposed =>
      relationalEntryOf
        iupacP93CanonicalFullereneC70SuperimposedAuthoritySource
        iupacP93CanonicalFullereneAuthoritySources_all_structurallyWellFormed.2.2.2.2
        (.fullerene .superimposedStereogenicElements) (by decide)
        { payload := .fullerene
            (.superimposed iupacP93CanonicalFullereneC70SuperimposedAuthorityObservation)
          validFor := by
            constructor
            · simp [P93ClausePayloadData.toClaims, P93FullereneClausePayload.toClaims]
            · exact iupacP93CanonicalFullereneC70SuperimposedAuthorityObservation_valid }
        83 (by decide) (by decide) "P-93.5.6.6" rfl
        "Superimposition of stereogenic elements in a fullerene molecule"
        "tetrakis[(1S)-1-phenylbutyl] (f,sC)-3′H,3′′H-dicyclopropa[8,25:33,34]-(C70-D5h(6))[5,6]fullerene-3′,3′,3′′,3′′-tetracarboxylate (PIN)"
        "PDF page 83, P-93.5.6.6, example and enantiomer names with adjacent diagram"
        (by decide) (by decide) (by decide)

@[simp] theorem relationalEntry_clause_exact
    (row : P93RelationalFullereneReleaseRow) :
    (relationalEntry row).clause = relationalClause row := by
  cases row <;> rfl

@[simp] theorem relationalEntry_source_exact
    (row : P93RelationalFullereneReleaseRow) :
    (relationalEntry row).source =
      (iupacP93CanonicalFullereneRelationalSourceAudit.row row).source := by
  cases row <;> rfl

/-- The relational release table is derived from the exhaustive five-row index. -/
def relationalEntries : List P93CanonicalClauseObservationEntry :=
  P93RelationalFullereneReleaseRow.all.map relationalEntry

/-- The complete fullerene source block: one legacy methodology row and five direct relational
rows. -/
def entries : List P93CanonicalClauseObservationEntry :=
  methodologyEntry :: relationalEntries

def coveredClauses : List P93Clause :=
  entries.map fun entry => entry.clause

@[simp] theorem entries_length : entries.length = 6 := by
  simp [entries, relationalEntries]

/-- The six emitted clause tags are exactly the reviewed fullerene partition, in its frozen order. -/
theorem coveredClauses_exact :
    coveredClauses =
      Remaining71P93FullereneAuthorityRow.all.map fun row => (.fullerene row : P93Clause) := by
  rfl

theorem coveredClauses_nodup : coveredClauses.Nodup := by
  rw [coveredClauses_exact]
  decide

def sources : List AuthoritativeChemicalInput :=
  entries.map fun entry => entry.source

private theorem methodologySource_ne_of_topologyAgreement
    (molecule : RawMolecule) (carrier : Finset Nat) (source : AuthoritativeChemicalInput)
    (agreement : molecule.MolecularFullereneTopologyRepresentationAgreement carrier none source)
    (moleculeNonempty : 0 < molecule.atomCount) :
    methodologySource ≠ source := by
  intro sourceEq
  have semanticCount :=
    molecule.toMolecularFullereneTopologySemanticMolecule?_atomCount
      carrier source.molecule agreement.1
  have sourceCountEq :=
    congrArg (fun input : AuthoritativeChemicalInput => input.molecule.atomCount) sourceEq
  have methodologyCount : methodologySource.molecule.atomCount = 0 := rfl
  change methodologySource.molecule.atomCount = source.molecule.atomCount at sourceCountEq
  rw [methodologyCount, semanticCount] at sourceCountEq
  exact (Nat.ne_of_gt moleculeNonempty) sourceCountEq.symm

private theorem methodologySource_ne_relationalSource
    (row : P93RelationalFullereneReleaseRow) :
    methodologySource ≠
      (iupacP93CanonicalFullereneRelationalSourceAudit.row row).source := by
  cases row with
  | inherentParent =>
      exact methodologySource_ne_of_topologyAgreement _ _
        iupacP93CanonicalFullereneC76Type1AuthoritySource
        iupacP93CanonicalFullereneAuthoritySources_all_agree.1 (by decide)
  | inherentSubstitution =>
      exact methodologySource_ne_of_topologyAgreement _ _
        iupacP93CanonicalFullereneC60Type2AuthoritySource
        iupacP93CanonicalFullereneAuthoritySources_all_agree.2.1 (by decide)
  | noninherentSubstitution =>
      exact methodologySource_ne_of_topologyAgreement _ _
        iupacP93CanonicalFullereneC60Type3AuthoritySource
        iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.1 (by decide)
  | chiralSubstituents =>
      exact methodologySource_ne_of_topologyAgreement _ _
        iupacP93CanonicalFullereneC70Type4AuthoritySource
        iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.2.1 (by decide)
  | superimposed =>
      exact methodologySource_ne_of_topologyAgreement _ _
        iupacP93CanonicalFullereneC70SuperimposedAuthoritySource
        iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.2.2 (by decide)



theorem relationalEntries_sources_exact :
    relationalEntries.map (fun entry => entry.source) =
      P93RelationalFullereneReleaseRow.all.map fun row =>
        (iupacP93CanonicalFullereneRelationalSourceAudit.row row).source := by
  rfl

theorem sources_nodup : sources.Nodup := by
  rw [sources, entries, List.map_cons, relationalEntries_sources_exact, List.nodup_cons]
  constructor
  · simp only [List.mem_map]
    rintro ⟨row, _rowPresent, sourceEq⟩
    exact methodologySource_ne_relationalSource row sourceEq.symm
  · exact iupacP93CanonicalFullereneRelationalSourceAudit.sourcesNodup

/-- Exact source-key invariant required when this block is appended to the canonical source
program.  Since all six rows have the fullerene family, source injectivity is the sharp form. -/
theorem observationSourceUnique :
    ∀ first ∈ entries, ∀ second ∈ entries,
      first.source = second.source → first = second := by
  have entriesNodup : entries.Nodup := by
    exact List.Nodup.of_map
      (fun entry : P93CanonicalClauseObservationEntry => entry.source) sources_nodup
  exact (List.nodup_map_iff_inj_on entriesNodup).mp sources_nodup

end
end P93CanonicalProgramFullerene
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.coveredClauses_exact
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFullerene.observationSourceUnique
