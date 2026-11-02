import TetraStereo.OneCenter.IUPACP93CanonicalSourceClaims
import TetraStereo.OneCenter.IUPACP93CanonicalProgramMonocyclicText
import TetraStereo.OneCenter.IUPACP93CanonicalProgramVonBaeyerSpiro
import TetraStereo.OneCenter.IUPACP93CanonicalProgramFusedCyclophane
import TetraStereo.OneCenter.IUPACP93CanonicalProgramRingAssembly

set_option autoImplicit false

/-!
# Concrete canonical P-93 cyclic source entries

This module joins twenty-six complete cyclic examples from the verified P-9 transcription: all
nine monocyclic rows, all nine von-Baeyer/spiro rows, five fused/cyclophane rows,
and three ring-assembly rows.  Seven monocyclic entries are supplied by
`IUPACP93CanonicalProgramMonocyclicText`; the two original entries are:

* P-93.5.1.4.1: `(E)-cyclononene (PIN)`;
* P-93.5.1.4.1: `(1E,1M)-cyclooct-1-ene (PIN)`.

The molecule graphs below transcribe the corresponding single-double-bond carbon rings.  The two
geometry-dependent rows retain separate printed observations and executable rational witnesses;
the reconstructed coordinates are not claimed as printed source data.
-/

namespace TetraStereo.OneCenter

open BlueBookP93
open BlueBookP93.Acyclic
open BlueBookP93.Cyclic
open IUPACNormativeProvision

namespace P93CanonicalProgramCyclic

def carbon : PeriodicElement where
  atomicNumber := 6
  positive := by decide
  atMost118 := by decide

def carbonAtom : SemanticAtom where
  element := carbon

def binaryInteraction (left right order : Nat) : SemanticInteraction where
  participants := [left, right]
  kind := .covalent order

/-! ## The explicitly named cyclooctene example -/

def cycloocteneSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := List.replicate 8 carbonAtom
      interactions :=
        [ binaryInteraction 0 1 2
        , binaryInteraction 1 2 1
        , binaryInteraction 2 3 1
        , binaryInteraction 3 4 1
        , binaryInteraction 4 5 1
        , binaryInteraction 5 6 1
        , binaryInteraction 6 7 1
        , binaryInteraction 7 0 1 ] }

def cycloocteneRing : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]

theorem cycloocteneSource_structurallyWellFormed :
    cycloocteneSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    cycloocteneSource).mp (by decide)

theorem cycloocteneRing_closed :
    P93AuthorityClosedCycle cycloocteneSource cycloocteneRing := by
  simp [P93AuthorityClosedCycle, cycloocteneRing, cycloocteneSource,
    binaryInteraction, P93AuthorityConnectedPath, P93AuthorityBinaryBond,
    P93AuthorityBinaryInteractionKind, P93AuthorityAtomsBounded,
    SemanticMolecule.atomCount]

theorem cycloocteneBond : P93AuthorityBinaryBond cycloocteneSource 0 1 := by
  simp [P93AuthorityBinaryBond, cycloocteneSource, binaryInteraction,
    P93AuthorityBinaryInteractionKind]

theorem cycloocteneBond_envelope :
    P93CanonicalPhysicalUnitEnvelope cycloocteneSource (.bond 0 1) := by
  exact ⟨by decide, by decide, by decide, cycloocteneBond⟩

/-- P-93.5.1.4.1 explicitly prints `(1E,1M)-cyclooct-1-ene (PIN)`. -/
def unsaturatedPayload : P93MonocyclicClausePayload .unsaturatedMonocycles :=
  .unsaturated ⟨cycloocteneRing, .bond 0 1⟩
    .ordinaryCyclicDoubleBondSystem 1 .M true

theorem unsaturatedPayload_valid :
    (P93ClausePayloadData.monocyclic unsaturatedPayload).ValidFor cycloocteneSource := by
  refine ⟨?_, cycloocteneRing_closed, rfl, ?_⟩
  · intro claim claimMem
    simp [P93ClausePayloadData.toClaims, unsaturatedPayload,
      P93MonocyclicClausePayload.toClaims,
      P93MonocyclicPhysicalPayload.baseClaims] at claimMem
    rcases claimMem with rfl | rfl | rfl | rfl
    · exact cycloocteneRing_closed
    · exact ⟨cycloocteneRing_closed, cycloocteneBond_envelope⟩
    · exact ⟨cycloocteneRing_closed, cycloocteneBond_envelope⟩
    · exact cycloocteneBond_envelope
  · simp [PreferredChiralCycloalkeneDescriptor]

def unsaturatedObservation :
    P93ClauseObservation cycloocteneSource (.monocyclic .unsaturatedMonocycles) where
  payload := .monocyclic unsaturatedPayload
  validFor := unsaturatedPayload_valid

/-- Frozen textual observation on PDF page 63.  The printed PIN contains both `1E` and `1M`, so
the helical assignment does not depend on reconstructing perspective from the drawing. -/
def unsaturatedTranscription : P93CanonicalSourceTranscription cycloocteneSource
    (.monocyclic .unsaturatedMonocycles) unsaturatedObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 :=
    "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 63
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.1.4"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.1.4.1"
  observationSubsectionNonempty := by decide
  printedObservation := "(1E,1M)-cyclooct-1-ene (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _claimMem
    exact
      { supportingLocator := "PDF page 63, P-93.5.1.4.1, named example and adjacent structure"
        supportingLocatorNonempty := by decide
        supportingObservation := "(1E,1M)-cyclooct-1-ene (PIN)"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

/-! ## The explicitly named cyclononene example -/

def cyclononeneSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := List.replicate 9 carbonAtom
      interactions :=
        [ binaryInteraction 0 1 2
        , binaryInteraction 1 2 1
        , binaryInteraction 2 3 1
        , binaryInteraction 3 4 1
        , binaryInteraction 4 5 1
        , binaryInteraction 5 6 1
        , binaryInteraction 6 7 1
        , binaryInteraction 7 8 1
        , binaryInteraction 8 0 1 ] }

def cyclononeneRing : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8]

theorem cyclononeneSource_structurallyWellFormed :
    cyclononeneSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    cyclononeneSource).mp (by decide)

theorem cyclononeneRing_closed :
    P93AuthorityClosedCycle cyclononeneSource cyclononeneRing := by
  simp [P93AuthorityClosedCycle, cyclononeneRing, cyclononeneSource,
    binaryInteraction, P93AuthorityConnectedPath, P93AuthorityBinaryBond,
    P93AuthorityBinaryInteractionKind, P93AuthorityAtomsBounded,
    SemanticMolecule.atomCount]

theorem cyclononeneBond : P93AuthorityBinaryBond cyclononeneSource 0 1 := by
  simp [P93AuthorityBinaryBond, cyclononeneSource, binaryInteraction,
    P93AuthorityBinaryInteractionKind]

theorem cyclononeneBond_envelope :
    P93CanonicalPhysicalUnitEnvelope cyclononeneSource (.bond 0 1) := by
  exact ⟨by decide, by decide, by decide, cyclononeneBond⟩

/-- P-93.5.1.4.1 explicitly prints `(E)-cyclononene (PIN)`. -/
def cyclicDoublePayload : P93MonocyclicClausePayload .cyclicDoubleBonds :=
  .cyclicDouble ⟨cyclononeneRing, .bond 0 1⟩ 1 .opposite (some .E)

theorem cyclicDoublePayload_valid :
    (P93ClausePayloadData.monocyclic cyclicDoublePayload).ValidFor cyclononeneSource := by
  refine ⟨?_, cyclononeneRing_closed, ⟨0, 1, rfl⟩, ?_⟩
  · intro claim claimMem
    simp [P93ClausePayloadData.toClaims, cyclicDoublePayload,
      P93MonocyclicClausePayload.toClaims,
      P93MonocyclicPhysicalPayload.baseClaims] at claimMem
    rcases claimMem with rfl | rfl | rfl | rfl
    · exact cyclononeneRing_closed
    · exact ⟨cyclononeneRing_closed, cyclononeneBond_envelope⟩
    · exact ⟨cyclononeneRing_closed, cyclononeneBond_envelope⟩
    · exact cyclononeneBond_envelope
  · rfl

def cyclicDoubleObservation :
    P93ClauseObservation cyclononeneSource (.monocyclic .cyclicDoubleBonds) where
  payload := .monocyclic cyclicDoublePayload
  validFor := cyclicDoublePayload_valid

/-- Frozen textual observation on PDF page 62.  The printed `E` is linked to the payload's
`opposite` senior-ligand source claim; `cyclicDoublePayload_valid` proves that this geometry assigns
exactly the stored `E` descriptor. -/
def cyclicDoubleTranscription : P93CanonicalSourceTranscription cyclononeneSource
    (.monocyclic .cyclicDoubleBonds) cyclicDoubleObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 :=
    "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 62
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.1.4.1"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.1.4.1"
  observationSubsectionNonempty := by decide
  printedObservation := "(E)-cyclononene (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _claimMem
    exact
      { supportingLocator := "PDF page 62, P-93.5.1.4.1, named example and adjacent structure"
        supportingLocatorNonempty := by decide
        supportingObservation := "(E)-cyclononene (PIN)"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

/-! ## Proof-carrying entries and exact coverage -/

def unsaturatedEntry : P93CanonicalClauseObservationEntry where
  source := cycloocteneSource
  sourceAdmitted := cycloocteneSource_structurallyWellFormed
  clause := .monocyclic .unsaturatedMonocycles
  clauseListed := by
    simp [P93Clause.all, Remaining71P93ClosedProductionRow.all,
      Remaining71P93ClosedProductionRow.monocyclicRows,
      Remaining71P93MonocyclicAuthorityRow.all]
  observation := unsaturatedObservation
  transcription := unsaturatedTranscription

def cyclicDoubleEntry : P93CanonicalClauseObservationEntry where
  source := cyclononeneSource
  sourceAdmitted := cyclononeneSource_structurallyWellFormed
  clause := .monocyclic .cyclicDoubleBonds
  clauseListed := by
    simp [P93Clause.all, Remaining71P93ClosedProductionRow.all,
      Remaining71P93ClosedProductionRow.monocyclicRows,
      Remaining71P93MonocyclicAuthorityRow.all]
  observation := cyclicDoubleObservation
  transcription := cyclicDoubleTranscription

def entries : List P93CanonicalClauseObservationEntry :=
  [ P93CanonicalProgramMonocyclicText.configurationEntry
  , P93CanonicalProgramMonocyclicText.absoluteEntry
  , P93CanonicalProgramMonocyclicText.achiralEntry
  , P93CanonicalProgramMonocyclicText.cisTransEntry
  , P93CanonicalProgramMonocyclicText.rctEntry
  , unsaturatedEntry
  , cyclicDoubleEntry
  , P93CanonicalProgramMonocyclicText.exocyclicEZEntry
  , P93CanonicalProgramMonocyclicText.exocyclicOtherEntry
  , P93CanonicalProgramVonBaeyerSpiro.vonBaeyerCIPEntry
  , P93CanonicalProgramVonBaeyerSpiro.vonBaeyerBridgeEntry
  , P93CanonicalProgramVonBaeyerSpiro.vonBaeyerRelativeEntry
  , P93CanonicalProgramVonBaeyerSpiro.vonBaeyerDoubleEntry
  , P93CanonicalProgramVonBaeyerSpiro.xabcdEntry
  , P93CanonicalProgramVonBaeyerSpiro.xababEntry
  , P93CanonicalProgramVonBaeyerSpiro.spiroDoubleEntry
  , P93CanonicalProgramVonBaeyerSpiro.axialEntry
  , P93CanonicalProgramVonBaeyerSpiro.tbpyEntry ] ++
    P93CanonicalProgramFusedCyclophane.entries ++
      P93CanonicalProgramRingAssembly.entries

def coveredClauses : List P93Clause := entries.map (·.clause)

@[simp] theorem entries_length : entries.length = 26 := rfl

@[simp] theorem entries_clause_exact : entries.map (·.clause) =
    (Remaining71P93MonocyclicAuthorityRow.all.map
      (fun row => (.monocyclic row : P93Clause))) ++
    (Remaining71P93VonBaeyerAuthorityRow.all.map
      (fun row => (.vonBaeyer row : P93Clause))) ++
    (Remaining71P93SpiroReadyAuthorityRow.all.map
      (fun row => (.spiro row : P93Clause))) ++ [.spiroNontetrahedral] ++
    [ .fusedCyclophane .fusedBridgedCIP
    , .fusedCyclophane .cisoidTransoid
    , .fusedCyclophane .cyclophanePlanes
    , .fusedCyclophane .cyclophaneCenters
    , .fusedCyclophane .cyclophaneDoubleBonds ] ++
    [ .ringAssembly .axes
    , .ringAssembly .centers
    , .ringAssembly .doubleBonds ] := rfl

theorem entry_sources_nodup : (entries.map fun entry => entry.source).Nodup := by
  decide

theorem entries_source_unique :
    ∀ first ∈ entries, ∀ second ∈ entries,
      first.source = second.source → first = second := by
  exact List.inj_on_of_nodup_map entry_sources_nodup

theorem coveredClause_has_entry (clause : P93Clause) (member : clause ∈ coveredClauses) :
    ∃ entry ∈ entries, entry.clause = clause := by
  change clause ∈ entries.map (·.clause) at member
  exact List.mem_map.mp member

/-- All non-fullerene, non-coupled cyclic clauses now have authoritative source entries. -/
def externallyBlockedClauses : List P93Clause := []

def requestedClauses : List P93Clause := coveredClauses ++ externallyBlockedClauses

/-- Canonical family-owned universe for this partial program: all cyclic P-93 rows except the
six fullerene rows and the coupled ring/chain row, which are owned by a separate source package. -/
def canonicalRequestedClauses : List P93Clause :=
  (Remaining71P93MonocyclicAuthorityRow.all.map .monocyclic) ++
  (Remaining71P93VonBaeyerAuthorityRow.all.map .vonBaeyer) ++
  (Remaining71P93SpiroReadyAuthorityRow.all.map .spiro) ++
  [.spiroNontetrahedral] ++
  (Remaining71P93FusedCyclophaneAuthorityRow.all.map .fusedCyclophane) ++
  (Remaining71P93RingAssemblyAuthorityRow.all.map .ringAssembly)

@[simp] theorem externallyBlockedClauses_length :
    externallyBlockedClauses.length = 0 := rfl

@[simp] theorem requestedClauses_length : requestedClauses.length = 26 := rfl

theorem requestedClauses_nodup : requestedClauses.Nodup := by
  decide

theorem covered_blocked_disjoint :
    List.Disjoint coveredClauses externallyBlockedClauses := by
  simp [coveredClauses, externallyBlockedClauses]

/-- The covered/blocked partition is extensionally the exact canonical 26-row family universe;
an omitted or substituted clause cannot pass merely by preserving the list length. -/
theorem requestedClauses_canonical_exact :
    requestedClauses.toFinset = canonicalRequestedClauses.toFinset := by
  apply Finset.ext
  intro clause
  simp only [List.mem_toFinset]
  cases clause with
  | fullerene row => cases row <;> simp [requestedClauses, coveredClauses,
      externallyBlockedClauses, canonicalRequestedClauses]
  | noncarbon row => cases row <;> simp [requestedClauses, coveredClauses,
      externallyBlockedClauses, canonicalRequestedClauses]
  | general row => cases row <;> simp [requestedClauses, coveredClauses,
      externallyBlockedClauses, canonicalRequestedClauses]
  | monocyclic row => cases row <;> simp [requestedClauses, coveredClauses,
      externallyBlockedClauses, canonicalRequestedClauses,
      Remaining71P93MonocyclicAuthorityRow.all]
  | vonBaeyer row => cases row <;> simp [requestedClauses, coveredClauses,
      externallyBlockedClauses, canonicalRequestedClauses,
      Remaining71P93VonBaeyerAuthorityRow.all]
  | ringAssembly row => cases row <;> simp [requestedClauses, coveredClauses,
      externallyBlockedClauses, canonicalRequestedClauses,
      Remaining71P93RingAssemblyAuthorityRow.all]
  | acyclic row => cases row <;> simp [requestedClauses, coveredClauses,
      externallyBlockedClauses, canonicalRequestedClauses]
  | spiro row => cases row <;> simp [requestedClauses, coveredClauses,
      externallyBlockedClauses, canonicalRequestedClauses,
      Remaining71P93SpiroReadyAuthorityRow.all]
  | spiroNontetrahedral => simp [requestedClauses, coveredClauses,
      externallyBlockedClauses, canonicalRequestedClauses]
  | fusedCyclophane row => cases row <;> simp [requestedClauses, coveredClauses,
      externallyBlockedClauses, canonicalRequestedClauses,
      Remaining71P93FusedCyclophaneAuthorityRow.all]
  | coupledRingChain row => cases row; simp [requestedClauses, coveredClauses,
      externallyBlockedClauses, canonicalRequestedClauses]

end P93CanonicalProgramCyclic
end TetraStereo.OneCenter
