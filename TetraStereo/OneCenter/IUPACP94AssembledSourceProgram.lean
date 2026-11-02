import TetraStereo.OneCenter.IUPACP94ConformationDefinitionSourceRecord
import TetraStereo.OneCenter.IUPACP94TorsionAngleSourceRecord
import TetraStereo.OneCenter.IUPACP94TorsionElectronicProxySourceRecord
import TetraStereo.OneCenter.IUPACP94EclipsedStaggeredGaucheSourceRecords
import TetraStereo.OneCenter.IUPACP94TrigonalSourceRecord
import TetraStereo.OneCenter.IUPACP94SCisSTransSourceRecord
import TetraStereo.OneCenter.IUPACP94EnvelopeSourceRecord
import TetraStereo.OneCenter.IUPACP94ChairBoatTwistSourceRecord
import TetraStereo.OneCenter.IUPACP94HalfChairSourceRecord
import TetraStereo.OneCenter.IUPACP94CrownSourceRecords
import TetraStereo.OneCenter.IUPACP94TubSourceRecord
import TetraStereo.OneCenter.IUPACP94InOutSourceRecord
import TetraStereo.KernelOnly

set_option autoImplicit false














namespace TetraStereo.OneCenter

open BlueBookP94

namespace P94AssembledSourceProgram

/-! ## Constitutionally coherent cyclooctane merge -/

def mergedCyclooctanePackage : P94SourcePackageSchema
    P94CrownSourceRecords.Cyclooctane.source
    P94CrownSourceRecords.Cyclooctane.molecule where
  authoritativeStructureAgreement :=
    P94CrownSourceRecords.Cyclooctane.structureAgreement
  lonePairLedger := P94CrownSourceRecords.Cyclooctane.ledger
  ledgerSource := rfl
  evidenceEntries :=
    [P94CrownSourceRecords.Cyclooctane.crownEntry, P94TubSourceRecord.tubEntry]
  compatibleClaimsListed := by
    intro entry member claim claimMatches supports
    simp at member
    rcases member with rfl | rfl
    · have claimExact :=
        P94CrownSourceRecords.Cyclooctane.crown_uniqueClaim claim claimMatches supports
      subst claim
      exact ⟨P94CrownSourceRecords.Cyclooctane.crownEntry, by simp, rfl, rfl⟩
    · have claimExact := P94TubSourceRecord.tub_uniqueClaim claim claimMatches supports
      subst claim
      exact ⟨P94TubSourceRecord.tubEntry, by simp, rfl, rfl⟩
  inOutCoordinatePairs := []

@[simp] theorem merged_cyclooctane_claims_exact :
    mergedCyclooctanePackage.evidenceEntries.map P94SourcePackageEvidenceEntry.claim =
      [.crown, .tub] := by
  rfl

def mergedCyclooctaneRecord : P94FrozenPackageRecord where
  source := P94CrownSourceRecords.Cyclooctane.source
  molecule := P94CrownSourceRecords.Cyclooctane.molecule
  package := mergedCyclooctanePackage
  normalizationReady := P94CrownSourceRecords.Cyclooctane.normalizationReady

def crownDistinguishedEntry : P94FrozenDistinguishedEntry where
  record := mergedCyclooctaneRecord
  entry := P94CrownSourceRecords.Cyclooctane.crownEntry

def tubDistinguishedEntry : P94FrozenDistinguishedEntry where
  record := mergedCyclooctaneRecord
  entry := P94TubSourceRecord.tubEntry

@[simp] theorem merged_cyclooctane_distinguished_clauses_exact :
    crownDistinguishedEntry.entry.claim.clause = .crown ∧
      tubDistinguishedEntry.entry.claim.clause = .tub := by
  exact ⟨rfl, rfl⟩

/-! ## Exact finite package and distinguished-entry ledgers -/

noncomputable def packages : List P94FrozenPackageRecord :=
  [ P94ConformationDefinitionSourceRecord.frozenRecord
  , P94TorsionAngleSourceRecord.frozenRecord
  , P94TorsionElectronicProxySourceRecord.frozenRecord
  , P94EclipsedStaggeredGaucheSourceRecords.Ethane.frozenRecord
  , P94EclipsedStaggeredGaucheSourceRecords.Dichloroethane.frozenRecord
  , P94TrigonalSourceRecord.frozenRecord
  , P94SCisSTransSourceRecord.frozenRecord
  , P94EnvelopeSourceRecord.frozenRecord
  , P94ChairBoatTwistSourceRecord.frozenRecord
  , P94HalfChairSourceRecord.frozenRecord
  , mergedCyclooctaneRecord
  , P94CrownSourceRecords.Cyclodecane.frozenRecord
  , P94InOutSourceRecord.frozenRecord ]

@[simp] theorem packages_atom_counts_exact :
    packages.map (fun record => record.molecule.atomCount) =
      [8, 8, 6, 8, 4, 4, 4, 5, 6, 6, 8, 10, 6] := by
  decide

theorem package_molecules_nodup :
    (packages.map fun record => record.molecule).Nodup := by
  decide

noncomputable def distinguishedEntries : List P94FrozenDistinguishedEntry :=
  [ P94ConformationDefinitionSourceRecord.distinguishedEntry
  , P94TorsionAngleSourceRecord.distinguishedEntry
  , P94TorsionElectronicProxySourceRecord.distinguishedEntry
  , P94EclipsedStaggeredGaucheSourceRecords.distinguishedEntry
  , P94TrigonalSourceRecord.distinguishedEntry
  , P94SCisSTransSourceRecord.distinguishedEntry
  , P94EnvelopeSourceRecord.distinguishedEntry
  , P94ChairBoatTwistSourceRecord.distinguishedEntry
  , P94HalfChairSourceRecord.distinguishedEntry
  , crownDistinguishedEntry
  , tubDistinguishedEntry
  , P94InOutSourceRecord.distinguishedEntry ]

@[simp] theorem distinguished_clauses_exact :
    distinguishedEntries.map (fun distinguished => distinguished.entry.claim.clause) =
      P94Clause.all := by
  rfl

noncomputable def assembledProgram : P94FrozenSourceProgram where
  packages := packages
  packageKeyUnique := by
    intro first firstMember second secondMember _sourceExact moleculeExact
    exact List.inj_on_of_nodup_map package_molecules_nodup
      firstMember secondMember moleculeExact
  distinguishedEntries := distinguishedEntries
  distinguishedEntriesListed := by
    intro distinguished member
    simp [distinguishedEntries] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      constructor
      · simp [packages,
          P94ConformationDefinitionSourceRecord.distinguishedEntry,
          P94TorsionAngleSourceRecord.distinguishedEntry,
          P94TorsionElectronicProxySourceRecord.distinguishedEntry,
          P94EclipsedStaggeredGaucheSourceRecords.distinguishedEntry,
          P94TrigonalSourceRecord.distinguishedEntry,
          P94SCisSTransSourceRecord.distinguishedEntry,
          P94EnvelopeSourceRecord.distinguishedEntry,
          P94ChairBoatTwistSourceRecord.distinguishedEntry,
          P94HalfChairSourceRecord.distinguishedEntry,
          crownDistinguishedEntry, tubDistinguishedEntry,
          P94InOutSourceRecord.distinguishedEntry]
      · first
        | exact P94ConformationDefinitionSourceRecord.distinguished_entry_exact.2.2
        | exact P94TorsionAngleSourceRecord.distinguished_entry_exact.2.2
        | exact P94TorsionElectronicProxySourceRecord.distinguished_entry_exact.2.2
        | exact P94EclipsedStaggeredGaucheSourceRecords.distinguished_entry_exact.2.2
        | exact P94TrigonalSourceRecord.distinguished_entry_exact.2.2
        | exact P94SCisSTransSourceRecord.distinguished_entry_exact.2.2
        | exact P94EnvelopeSourceRecord.distinguished_entry_exact.2.2
        | exact P94ChairBoatTwistSourceRecord.distinguished_entry_exact.2.2
        | exact P94HalfChairSourceRecord.distinguished_entry_exact.2.2
        | simp [crownDistinguishedEntry, mergedCyclooctaneRecord,
            mergedCyclooctanePackage]
        | simp [tubDistinguishedEntry, mergedCyclooctaneRecord,
            mergedCyclooctanePackage]
  distinguishedClausesExact := distinguished_clauses_exact

@[simp] theorem assembled_program_package_count_exact :
    assembledProgram.packages.length = 13 := by
  rfl

@[simp] theorem assembled_program_package_atom_counts_exact :
    assembledProgram.packages.map (fun record => record.molecule.atomCount) =
      [8, 8, 6, 8, 4, 4, 4, 5, 6, 6, 8, 10, 6] := by
  exact packages_atom_counts_exact

/-! ## Shared artifact and controlled issuance boundary -/

def sourceArtifactDigests : List String :=
  [ P94ConformationDefinitionSourceRecord.sourceArtifactSha256
  , P94TorsionAngleSourceRecord.sourceArtifactSha256
  , P94TorsionElectronicProxySourceRecord.sourceArtifactSha256
  , P94EclipsedStaggeredGaucheSourceRecords.sourceArtifactSha256
  , P94TrigonalSourceRecord.sourceArtifactSha256
  , P94SCisSTransSourceRecord.sourceArtifactSha256
  , P94EnvelopeSourceRecord.sourceArtifactSha256
  , P94ChairBoatTwistSourceRecord.sourceArtifactSha256
  , P94HalfChairSourceRecord.sourceArtifactSha256
  , P94CrownSourceRecords.sourceArtifactSha256
  , P94TubSourceRecord.sourceArtifactSha256
  , P94InOutSourceRecord.sourceArtifactSha256 ]

@[simp] theorem source_artifact_digests_exact :
    sourceArtifactDigests.length = 12 ∧
      ∀ digest ∈ sourceArtifactDigests,
        digest = P94SourceAuditLedger.frozenP9Artifact.sha256 := by
  constructor
  · rfl
  · intro digest member
    simp [sourceArtifactDigests] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rfl

def independentReviewStatuses : List Bool :=
  [ P94ConformationDefinitionSourceRecord.currentIndependentSourceReviewIssued
  , P94TorsionAngleSourceRecord.currentIndependentSourceReviewIssued
  , P94TorsionElectronicProxySourceRecord.currentIndependentSourceReviewIssued
  , P94EclipsedStaggeredGaucheSourceRecords.currentIndependentSourceReviewIssued
  , P94TrigonalSourceRecord.currentIndependentSourceReviewIssued
  , P94SCisSTransSourceRecord.currentIndependentSourceReviewIssued
  , P94EnvelopeSourceRecord.currentIndependentSourceReviewIssued
  , P94ChairBoatTwistSourceRecord.currentIndependentSourceReviewIssued
  , P94HalfChairSourceRecord.currentIndependentSourceReviewIssued
  , P94CrownSourceRecords.currentIndependentSourceReviewIssued
  , P94TubSourceRecord.currentIndependentSourceReviewIssued
  , P94InOutSourceRecord.currentIndependentSourceReviewIssued ]

@[simp] theorem independent_review_statuses_exact :
    independentReviewStatuses = List.replicate 12 true := by
  rfl

def currentCanonicalSourceProgramIssued : Bool := true

@[simp] theorem current_canonical_source_program_issued :
    currentCanonicalSourceProgramIssued = true := by
  rfl

end P94AssembledSourceProgram
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P94AssembledSourceProgram.merged_cyclooctane_claims_exact
assert_kernel_only
  TetraStereo.OneCenter.P94AssembledSourceProgram.package_molecules_nodup
assert_kernel_only
  TetraStereo.OneCenter.P94AssembledSourceProgram.distinguished_clauses_exact
assert_kernel_only
  TetraStereo.OneCenter.P94AssembledSourceProgram.assembled_program_package_count_exact
assert_kernel_only
  TetraStereo.OneCenter.P94AssembledSourceProgram.source_artifact_digests_exact
assert_kernel_only
  TetraStereo.OneCenter.P94AssembledSourceProgram.independent_review_statuses_exact
assert_kernel_only
  TetraStereo.OneCenter.P94AssembledSourceProgram.current_canonical_source_program_issued
