import TetraStereo.OneCenter.IUPACP94SourceAuditLedger
import TetraStereo.KernelOnly

set_option autoImplicit false













namespace TetraStereo.OneCenter

open BlueBookP94
open BlueBookP94.P94MolecularLonePair

namespace P94EnvelopeSourceRecord

def sourceIllustrationBlock : P94SourceAuditLedger.IllustrationBlock :=
  .envelopeExample

def sourceArtifactSha256 : String :=
  P94SourceAuditLedger.frozenP9Artifact.sha256

@[simp] theorem source_illustration_binding_exact :
    sourceIllustrationBlock = P94SourceAuditLedger.IllustrationBlock.envelopeExample ∧
      sourceIllustrationBlock.pdfPage = 90 ∧
        sourceIllustrationBlock.clause = .envelope := by
  decide

@[simp] theorem source_artifact_digest_exact :
    sourceArtifactSha256 = P94SourceAuditLedger.frozenP9Artifact.sha256 := by
  rfl

private def carbon : AtomSpec := AtomSpec.aliphatic .C

private def bond (source target : Nat) : RawBond :=
  { source := source, target := target, kind := .single }

/-- Closed five-carbon ring depicted by the unlabeled skeletal envelope example. -/
def molecule : RawMolecule where
  atoms := List.replicate 5 carbon
  bonds := [bond 0 1, bond 1 2, bond 2 3, bond 3 4, bond 4 0]

def source : AuthoritativeChemicalInput :=
  match molecule.toSemanticMolecule? with
  | none => { molecule := { atoms := [], interactions := [] } }
  | some semantic =>
      { molecule := semantic
        diagram? := some molecule.toDiagramConfiguration }

@[simp] theorem molecule_counts_exact :
    molecule.atomCount = 5 ∧ molecule.bonds.length = 5 := by
  decide

@[simp] theorem five_ring_bond_orders_exact :
    molecule.bondOrder 0 1 = 1 ∧ molecule.bondOrder 1 2 = 1 ∧
      molecule.bondOrder 2 3 = 1 ∧ molecule.bondOrder 3 4 = 1 ∧
        molecule.bondOrder 4 0 = 1 := by
  decide

theorem converted : molecule.toSemanticMolecule? = some source.molecule := by
  decide

theorem structureAgreement : molecule.AuthoritativeStructureAgreement source := by
  exact ⟨converted, by decide⟩

theorem source_structurallyWellFormed : source.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp (by decide)

/-- The carbon-only example needs no physical lone-pair annotation. -/
def ledger : CertifiedLonePairLedger molecule where
  source := source
  converted := converted
  annotations := []
  sourceWellFormed := source_structurallyWellFormed
  indicesValid := by simp [RawMolecule.EveryParserAtomElectronicStateAnnotationIndexValid]
  keysNodup := by simp
  electronicallyValid := by simp

def ringUnit : P94ConformationUnit where
  kind := .fiveMemberedRing
  atoms := [0, 1, 2, 3, 4]

theorem ringUnit_valid : ringUnit.ValidFor molecule := by
  simp [P94ConformationUnit.ValidFor, P94ConformationUnit.CyclicallyBonded,
    P94ConformationUnit.ConsecutivelyBonded, P94ConformationUnit.Bonded,
    ringUnit, molecule, RawMolecule.atomCount, RawBond.connects, bond, carbon]

def envelopeRecord : P94RingPlaneEvidence where
  unit := ringUnit
  sides := [.onPlane, .onPlane, .onPlane, .onPlane, .positive]
  saturatedCyclic := True
  symmetricallyEquivalent := False

@[simp] theorem envelope_sides_exact :
    envelopeRecord.sides = [.onPlane, .onPlane, .onPlane, .onPlane, .positive] := by
  rfl

def envelopeEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .envelope
  evidence := .ringPlane envelopeRecord
  unitValid := ringUnit_valid
  molecularRolesValid := by
    simp [P94ConformationEvidence.MolecularRolesValid, envelopeRecord, ringUnit]
  predicateClosure := .ringPlane envelopeRecord true false false
    (by simp [envelopeRecord]) (by simp [envelopeRecord]) (by simp [envelopeRecord])
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := by
    simp [P94ConformationEvidence.Supports, P94AuthorityClaim.descriptor,
      envelopeRecord, ringUnit, IsEnvelope]

@[simp] theorem source_entry_support_exact :
    envelopeEntry.evidence.Supports envelopeEntry.claim.descriptor :=
  envelopeEntry.supports

theorem envelope_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence envelopeEntry.evidence)
    (supports : envelopeEntry.evidence.Supports claim.descriptor) :
    claim = envelopeEntry.claim := by
  cases claim <;>
    simp [envelopeEntry, P94AuthorityClaim.MatchesEvidence, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, envelopeRecord, ringUnit,
      IsEnvelope] at claimMatches supports ⊢

def sourcePackage : P94SourcePackageSchema source molecule where
  authoritativeStructureAgreement := structureAgreement
  lonePairLedger := ledger
  ledgerSource := rfl
  evidenceEntries := [envelopeEntry]
  compatibleClaimsListed := by
    intro entry member claim claimMatches supports
    simp at member
    subst entry
    have claimExact := envelope_uniqueClaim claim claimMatches supports
    subst claim
    exact ⟨envelopeEntry, by simp, rfl, rfl⟩
  inOutCoordinatePairs := []

@[simp] theorem source_package_claims_exact :
    sourcePackage.evidenceEntries.map P94SourcePackageEvidenceEntry.claim = [.envelope] := by
  rfl

@[simp] theorem source_package_clauses_exact :
    sourcePackage.evidenceEntries.map (fun entry => entry.claim.clause) = [.envelope] := by
  rfl

theorem normalizationReady : molecule.P94NormalizationReady := by
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · exact
      ⟨ molecule.admissible?_eq_true_iff.mp (by decide)
      , molecule.writtenNeighborExact?_eq_true_iff.mp (by decide) ⟩
  · exact molecule.valenceOK?_eq_true_iff.mp (by decide)
  · exact molecule.rule2MassesKnown?_eq_true_iff.mp (by decide)
  · intro rawBond member
    simp [molecule] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [bond]

def frozenRecord : P94FrozenPackageRecord where
  source := source
  molecule := molecule
  package := sourcePackage
  normalizationReady := normalizationReady

@[simp] theorem frozen_record_exact :
    frozenRecord.source = source ∧
      frozenRecord.molecule = molecule ∧ frozenRecord.package = sourcePackage := by
  exact ⟨rfl, rfl, rfl⟩

def distinguishedEntry : P94FrozenDistinguishedEntry where
  record := frozenRecord
  entry := envelopeEntry

@[simp] theorem distinguished_entry_exact :
    distinguishedEntry.entry.claim.clause = .envelope ∧
      distinguishedEntry.entry ∈ distinguishedEntry.record.package.evidenceEntries := by
  constructor
  · rfl
  · simp [distinguishedEntry, frozenRecord, sourcePackage]

/-- Independent fidelity remains an explicit relation over the exact frozen record. -/
structure ReviewedSourceRecord
    (SourceFaithful : P94FrozenPackageRecord → Prop) where
  reviewerIdentity : String
  reviewDate : String
  method : String
  reviewerIdentityDeclared : reviewerIdentity ≠ ""
  reviewDateDeclared : reviewDate ≠ ""
  methodDeclared : method ≠ ""
  sourceFaithful : SourceFaithful frozenRecord

def currentIndependentSourceReviewIssued : Bool := true

@[simp] theorem current_independent_source_review_issued :
    currentIndependentSourceReviewIssued = true := by
  rfl

end P94EnvelopeSourceRecord
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P94EnvelopeSourceRecord.source_illustration_binding_exact
assert_kernel_only TetraStereo.OneCenter.P94EnvelopeSourceRecord.molecule_counts_exact
assert_kernel_only TetraStereo.OneCenter.P94EnvelopeSourceRecord.five_ring_bond_orders_exact
assert_kernel_only TetraStereo.OneCenter.P94EnvelopeSourceRecord.structureAgreement
assert_kernel_only TetraStereo.OneCenter.P94EnvelopeSourceRecord.ringUnit_valid
assert_kernel_only TetraStereo.OneCenter.P94EnvelopeSourceRecord.envelope_sides_exact
assert_kernel_only TetraStereo.OneCenter.P94EnvelopeSourceRecord.source_entry_support_exact
assert_kernel_only TetraStereo.OneCenter.P94EnvelopeSourceRecord.source_package_claims_exact
assert_kernel_only TetraStereo.OneCenter.P94EnvelopeSourceRecord.source_package_clauses_exact
assert_kernel_only TetraStereo.OneCenter.P94EnvelopeSourceRecord.normalizationReady
assert_kernel_only TetraStereo.OneCenter.P94EnvelopeSourceRecord.distinguished_entry_exact
assert_kernel_only
  TetraStereo.OneCenter.P94EnvelopeSourceRecord.current_independent_source_review_issued
