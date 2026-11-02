import TetraStereo.OneCenter.IUPACP93CanonicalProgramNoncarbonText

set_option autoImplicit false
set_option maxRecDepth 4096

/-!
# Complete verified textual P-93.2 source program

This module adds the three remaining noncarbon-tetrahedral rows to the four verified entries in
`IUPACP93CanonicalProgramNoncarbonText` and proves exact coverage and source-key uniqueness for
the complete seven-row P-93.2 family.
-/

namespace TetraStereo.OneCenter

open BlueBookP93
open BlueBookP93.NoncarbonTetrahedra
open IUPACNormativeProvision
open P93CanonicalProgramNoncarbonText

namespace P93CanonicalProgramNoncarbonTextComplete

def hydrogen : PeriodicElement where
  atomicNumber := 1
  positive := by decide
  atMost118 := by decide

def sodium : PeriodicElement where
  atomicNumber := 11
  positive := by decide
  atMost118 := by decide

def silicon : PeriodicElement where
  atomicNumber := 14
  positive := by decide
  atMost118 := by decide

def sulfur : PeriodicElement where
  atomicNumber := 16
  positive := by decide
  atMost118 := by decide

def isotopeAtom (element : PeriodicElement) (mass : Nat) : SemanticAtom where
  element := element
  isotopeMassNumber? := some mass

/-! ## P-93.2.4: phosphates, phosphonates, and related compounds -/

/-- Full constitution of sodium (R)-(O-methyl O-phenyl phosphorothioate).  The source's first
resonance form is retained: P=S, terminal P-O-, O-methyl, O-phenyl, and Na+ are explicit. -/
def phosphorusSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms :=
        [ atom phosphorus, atom sulfur, atom oxygen, atom oxygen, atom oxygen (-1)
        , atom carbon, atom carbon, atom carbon, atom carbon, atom carbon, atom carbon
        , atom carbon, atom sodium 1 ]
      interactions :=
        [ bond 0 1 2, bond 0 2 1, bond 0 3 1, bond 0 4 1
        , bond 2 5 1
        , bond 5 6 2, bond 6 7 1, bond 7 8 2
        , bond 8 9 1, bond 9 10 2, bond 10 5 1
        , bond 3 11 1 ] }

def phosphorusAssignment : P93NoncarbonAssignmentPayload where
  frame := { center := 0, ligands := [1, 2, 3, 4] }
  descriptor := .acyclic .R

def phosphorusChargeSeparated : FormalChargeArrangement where
  centerCharge := 0
  oxygenCharge := -1

def phosphorusNeutralOxo : FormalChargeArrangement where
  centerCharge := 0
  oxygenCharge := 0

theorem phosphorusSource_structurallyWellFormed : phosphorusSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff phosphorusSource).mp
    (by decide)

theorem phosphorusFrame_valid :
    phosphorusAssignment.frame.StructurallyValidFor phosphorusSource := by
  simp [P93NoncarbonTetrahedralFrame.StructurallyValidFor, phosphorusAssignment,
    phosphorusSource, P93AuthorityAtomsBounded, P93AuthorityBinaryBond,
    P93AuthorityMulticenterIncidence, P93AuthorityBinaryInteractionKind, bond,
    SemanticMolecule.atomCount, atom, phosphorus]
  intro ligand
  omega

def phosphorusPayload : P93NoncarbonClausePayload .phosphatesPhosphonates :=
  .phosphorus phosphorusAssignment 4 .related false true
    phosphorusChargeSeparated phosphorusNeutralOxo

theorem phosphorusPayload_valid :
    (P93ClausePayloadData.noncarbon phosphorusPayload).ValidFor phosphorusSource := by
  refine ⟨?_, phosphorusFrame_valid, ?_, by simp [phosphorusAssignment], ?_, ?_, ?_, rfl,
    trivial⟩
  · intro claim claimMember
    change claim ∈ phosphorusAssignment.baseClaims ++
      [ .noncarbon (.phosphorusOxo 0 4 .related false phosphorusChargeSeparated)
      , .noncarbon (.phosphorusOxo 0 4 .related true phosphorusNeutralOxo) ] at claimMember
    rw [List.mem_append] at claimMember
    rcases claimMember with baseMember | variantMember
    · exact assignmentBaseClaims_valid phosphorusAssignment phosphorusFrame_valid claim baseMember
    · simp at variantMember
      rcases variantMember with firstVariant | secondVariant
      · subst claim
        simp [P93SourceClaim.SourceEnvelope, P93NoncarbonClaim.SourceEnvelope,
          phosphorusSource, P93AuthorityBinaryBond, P93AuthorityBinaryInteractionKind, bond,
          SemanticMolecule.atomCount]
      · subst claim
        simp [P93SourceClaim.SourceEnvelope, P93NoncarbonClaim.SourceEnvelope,
          phosphorusSource, P93AuthorityBinaryBond, P93AuthorityBinaryInteractionKind, bond,
          SemanticMolecule.atomCount]
  · exact ⟨atom phosphorus, by simp [phosphorusAssignment, phosphorusSource], rfl⟩
  · exact ⟨atom oxygen (-1), by simp [phosphorusSource], rfl⟩
  · simp [phosphorusAssignment, phosphorusSource, P93AuthorityBinaryBond,
      P93AuthorityBinaryInteractionKind, bond]
  · decide

def phosphorusObservation : P93ClauseObservation phosphorusSource
    (.noncarbon .phosphatesPhosphonates) where
  payload := .noncarbon phosphorusPayload
  validFor := phosphorusPayload_valid

def phosphorusTranscription : P93CanonicalSourceTranscription phosphorusSource
    (.noncarbon .phosphatesPhosphonates) phosphorusObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := blueBookP9Sha256
  artifactSha256Exact := rfl
  pdfPage := 39
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.2.4"
  clauseSectionExact := rfl
  observationSubsection := "P-93.2.4"
  observationSubsectionNonempty := by decide
  printedObservation := "sodium (R)-(O-methyl O-phenyl phosphorothioate) (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro _claim _claimMember
    exact
      { supportingLocator := "PDF page 39, P-93.2.4 rule text and first resonance-pair example"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "The P=O bond is considered as a single bond and formal charge arrangement is not considered when determining configuration. sodium (R)-(O-methyl O-phenyl phosphorothioate) (PIN)."
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def phosphorusEntry : P93CanonicalClauseObservationEntry where
  source := phosphorusSource
  sourceAdmitted := phosphorusSource_structurallyWellFormed
  clause := .noncarbon .phosphatesPhosphonates
  clauseListed := by
    simp [P93Clause.all, Remaining71P93ClosedProductionRow.all,
      Remaining71P93ClosedProductionRow.noncarbonRows,
      Remaining71P93NoncarbonAuthorityRow.all]
  observation := phosphorusObservation
  transcription := phosphorusTranscription

/-! ## P-93.2.5: sulfates, sulfonates, and related compounds -/

/-- Full constitution of
1-methyl-4-[(R)-phenyl(18O1)methanesulfonyl]benzene.  Both sulfonyl oxygens, the para-tolyl
group, the benzyl carbon, the second phenyl ring, and the printed oxygen isotope are retained. -/
def chalcogenSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms :=
        [ atom sulfur, isotopeAtom oxygen 18, atom oxygen
        , atom carbon, atom carbon, atom carbon, atom carbon, atom carbon, atom carbon
        , atom carbon, atom carbon
        , atom carbon, atom carbon, atom carbon, atom carbon, atom carbon, atom carbon ]
      interactions :=
        [ bond 0 1 2, bond 0 2 2, bond 0 3 1, bond 0 10 1
        , bond 3 4 2, bond 4 5 1, bond 5 6 2
        , bond 6 7 1, bond 7 8 2, bond 8 3 1, bond 6 9 1
        , bond 10 11 1
        , bond 11 12 2, bond 12 13 1, bond 13 14 2
        , bond 14 15 1, bond 15 16 2, bond 16 11 1 ] }

def chalcogenAssignment : P93NoncarbonAssignmentPayload where
  frame := { center := 0, ligands := [1, 2, 3, 10] }
  descriptor := .acyclic .R

def chalcogenNeutralOxo : FormalChargeArrangement where
  centerCharge := 0
  oxygenCharge := 0

def chalcogenChargeSeparated : FormalChargeArrangement where
  centerCharge := 1
  oxygenCharge := -1

theorem chalcogenSource_structurallyWellFormed : chalcogenSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff chalcogenSource).mp
    (by decide)

theorem chalcogenFrame_valid :
    chalcogenAssignment.frame.StructurallyValidFor chalcogenSource := by
  simp [P93NoncarbonTetrahedralFrame.StructurallyValidFor, chalcogenAssignment,
    chalcogenSource, P93AuthorityAtomsBounded, P93AuthorityBinaryBond,
    P93AuthorityMulticenterIncidence, P93AuthorityBinaryInteractionKind, bond,
    SemanticMolecule.atomCount, isotopeAtom, atom, sulfur]
  intro ligand
  omega

def chalcogenPayload : P93NoncarbonClausePayload .sulfatesSulfonates :=
  .chalcogen chalcogenAssignment 1 .related true false
    chalcogenNeutralOxo chalcogenChargeSeparated

theorem chalcogenPayload_valid :
    (P93ClausePayloadData.noncarbon chalcogenPayload).ValidFor chalcogenSource := by
  refine ⟨?_, chalcogenFrame_valid, ?_, by simp [chalcogenAssignment], ?_, ?_, ?_, trivial,
    rfl, trivial⟩
  · intro claim claimMember
    change claim ∈ chalcogenAssignment.baseClaims ++
      [ .noncarbon (.chalcogenOxo 0 1 .related true chalcogenNeutralOxo)
      , .noncarbon (.chalcogenOxo 0 1 .related false chalcogenChargeSeparated) ] at claimMember
    rw [List.mem_append] at claimMember
    rcases claimMember with baseMember | variantMember
    · exact assignmentBaseClaims_valid chalcogenAssignment chalcogenFrame_valid claim baseMember
    · simp at variantMember
      rcases variantMember with firstVariant | secondVariant
      · subst claim
        simp [P93SourceClaim.SourceEnvelope, P93NoncarbonClaim.SourceEnvelope,
          chalcogenSource, P93AuthorityBinaryBond, P93AuthorityBinaryInteractionKind, bond,
          SemanticMolecule.atomCount]
      · subst claim
        simp [P93SourceClaim.SourceEnvelope, P93NoncarbonClaim.SourceEnvelope,
          chalcogenSource, P93AuthorityBinaryBond, P93AuthorityBinaryInteractionKind, bond,
          SemanticMolecule.atomCount]
  · exact ⟨atom sulfur, by simp [chalcogenAssignment, chalcogenSource],
      by simp [P93NoncarbonChalcogenOxoFamilyMatches, atom, sulfur]⟩
  · exact ⟨isotopeAtom oxygen 18, by simp [chalcogenSource], rfl⟩
  · simp [chalcogenAssignment, chalcogenSource, P93AuthorityBinaryBond,
      P93AuthorityBinaryInteractionKind, bond]
  · decide

def chalcogenObservation : P93ClauseObservation chalcogenSource
    (.noncarbon .sulfatesSulfonates) where
  payload := .noncarbon chalcogenPayload
  validFor := chalcogenPayload_valid

def chalcogenTranscription : P93CanonicalSourceTranscription chalcogenSource
    (.noncarbon .sulfatesSulfonates) chalcogenObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := blueBookP9Sha256
  artifactSha256Exact := rfl
  pdfPage := 40
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.2.5"
  clauseSectionExact := rfl
  observationSubsection := "P-93.2.5"
  observationSubsectionNonempty := by decide
  printedObservation := "1-methyl-4-[(R)-phenyl(18O1)methanesulfonyl]benzene (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro _claim _claimMember
    exact
      { supportingLocator := "PDF page 39, P-93.2.5 rule text; PDF page 40, first continued example/structure"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "Sulfates, sulfonates and related anions are treated in the same way as phosphate anions. 1-methyl-4-[(R)-phenyl(18O1)methanesulfonyl]benzene (PIN)."
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def chalcogenEntry : P93CanonicalClauseObservationEntry where
  source := chalcogenSource
  sourceAdmitted := chalcogenSource_structurallyWellFormed
  clause := .noncarbon .sulfatesSulfonates
  clauseListed := by
    simp [P93Clause.all, Remaining71P93ClosedProductionRow.all,
      Remaining71P93ClosedProductionRow.noncarbonRows,
      Remaining71P93NoncarbonAuthorityRow.all]
  observation := chalcogenObservation
  transcription := chalcogenTranscription

/-! ## P-93.2.6: Group 14 other than carbon -/

/-- Complete constitution of (R)-methyl(propyl)silanol.  Both hydrogens are explicit because the
Si-H bond is one of the four stereogenic ligands and the O-H bond is part of the named silanol. -/
def group14Source : AuthoritativeChemicalInput where
  molecule :=
    { atoms :=
        [ atom silicon, atom hydrogen, atom oxygen, atom hydrogen
        , atom carbon, atom carbon, atom carbon, atom carbon ]
      interactions :=
        [ bond 0 1 1, bond 0 2 1, bond 2 3 1, bond 0 4 1
        , bond 0 5 1, bond 5 6 1, bond 6 7 1 ] }

def group14Assignment : P93NoncarbonAssignmentPayload where
  frame := { center := 0, ligands := [1, 2, 4, 5] }
  descriptor := .acyclic .R

theorem group14Source_structurallyWellFormed : group14Source.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff group14Source).mp
    (by decide)

theorem group14Frame_valid :
    group14Assignment.frame.StructurallyValidFor group14Source := by
  simp [P93NoncarbonTetrahedralFrame.StructurallyValidFor, group14Assignment,
    group14Source, P93AuthorityAtomsBounded, P93AuthorityBinaryBond,
    P93AuthorityMulticenterIncidence, P93AuthorityBinaryInteractionKind, bond,
    SemanticMolecule.atomCount, atom, silicon]
  intro ligand
  omega

def group14Payload : P93NoncarbonClausePayload .group14Noncarbon :=
  .group14 group14Assignment .silicon

theorem group14Payload_valid :
    (P93ClausePayloadData.noncarbon group14Payload).ValidFor group14Source := by
  refine ⟨assignmentBaseClaims_valid group14Assignment group14Frame_valid,
    group14Frame_valid, ?_, trivial⟩
  exact ⟨atom silicon, by simp [group14Assignment, group14Source], rfl⟩

def group14Observation : P93ClauseObservation group14Source
    (.noncarbon .group14Noncarbon) where
  payload := .noncarbon group14Payload
  validFor := group14Payload_valid

def group14Transcription : P93CanonicalSourceTranscription group14Source
    (.noncarbon .group14Noncarbon) group14Observation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := blueBookP9Sha256
  artifactSha256Exact := rfl
  pdfPage := 40
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.2.6"
  clauseSectionExact := rfl
  observationSubsection := "P-93.2.6"
  observationSubsectionNonempty := by decide
  printedObservation := "(R)-methyl(propyl)silanol (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro _claim _claimMember
    exact
      { supportingLocator := "PDF page 40, P-93.2.6 rule text and sole example/structure"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "Chiral silanes, germanes, stannanes, and plumbanes are treated in the same way as carbon compounds. (R)-methyl(propyl)silanol (PIN)."
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def group14Entry : P93CanonicalClauseObservationEntry where
  source := group14Source
  sourceAdmitted := group14Source_structurallyWellFormed
  clause := .noncarbon .group14Noncarbon
  clauseListed := by
    simp [P93Clause.all, Remaining71P93ClosedProductionRow.all,
      Remaining71P93ClosedProductionRow.noncarbonRows,
      Remaining71P93NoncarbonAuthorityRow.all]
  observation := group14Observation
  transcription := group14Transcription

/-! ## Remaining-three and complete-seven program surfaces -/

def remainingEntries : List P93CanonicalClauseObservationEntry :=
  [phosphorusEntry, chalcogenEntry, group14Entry]

def remainingCoveredClauses : List P93Clause := remainingEntries.map fun entry => entry.clause

@[simp] theorem remainingEntries_length : remainingEntries.length = 3 := rfl

@[simp] theorem remainingCoveredClauses_exact : remainingCoveredClauses =
    [ .noncarbon .phosphatesPhosphonates
    , .noncarbon .sulfatesSulfonates
    , .noncarbon .group14Noncarbon ] := rfl

theorem remainingCoveredClauses_nodup : remainingCoveredClauses.Nodup := by decide

theorem remaining_entries_source_unique :
    ∀ first ∈ remainingEntries, ∀ second ∈ remainingEntries,
      first.source = second.source → first = second := by
  intro first firstMember second secondMember sourceExact
  simp [remainingEntries] at firstMember secondMember
  rcases firstMember with rfl | rfl | rfl <;>
    rcases secondMember with rfl | rfl | rfl <;> try rfl
  all_goals
    exfalso
    have atomCountExact := congrArg (fun input => input.molecule.atomCount) sourceExact
    norm_num [phosphorusEntry, chalcogenEntry, group14Entry,
      phosphorusSource, chalcogenSource, group14Source,
      SemanticMolecule.atomCount] at atomCountExact

def entries : List P93CanonicalClauseObservationEntry :=
  P93CanonicalProgramNoncarbonText.entries ++ remainingEntries

def coveredClauses : List P93Clause := entries.map fun entry => entry.clause

@[simp] theorem entries_length : entries.length = 7 := rfl

@[simp] theorem coveredClauses_exact : coveredClauses =
    Remaining71P93NoncarbonAuthorityRow.all.map fun row => (.noncarbon row : P93Clause) := rfl

theorem coveredClauses_nodup : coveredClauses.Nodup := by
  rw [coveredClauses_exact]
  decide

theorem covered_clause_has_entry (clause : P93Clause) (covered : clause ∈ coveredClauses) :
    ∃ entry ∈ entries, entry.clause = clause := by
  simpa [coveredClauses] using covered

theorem entries_source_unique :
    ∀ first ∈ entries, ∀ second ∈ entries,
      first.source = second.source → first = second := by
  intro first firstMember second secondMember sourceExact
  simp [entries, P93CanonicalProgramNoncarbonText.entries, remainingEntries] at firstMember secondMember
  rcases firstMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases secondMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try rfl
  all_goals
    exfalso
    have atomCountExact := congrArg (fun input => input.molecule.atomCount) sourceExact
    norm_num [P93CanonicalProgramNoncarbonText.phosphanoneEntry,
      P93CanonicalProgramNoncarbonText.methodologyEntry,
      P93CanonicalProgramNoncarbonText.azaniumEntry,
      P93CanonicalProgramNoncarbonText.oxideEntry,
      phosphorusEntry, chalcogenEntry, group14Entry,
      P93CanonicalProgramNoncarbonText.phosphanoneSource,
      P93CanonicalProgramNoncarbonText.methodologySource,
      P93CanonicalProgramNoncarbonText.azaniumSource,
      P93CanonicalProgramNoncarbonText.oxideSource,
      phosphorusSource, chalcogenSource, group14Source,
      SemanticMolecule.atomCount] at atomCountExact

end P93CanonicalProgramNoncarbonTextComplete
end TetraStereo.OneCenter
