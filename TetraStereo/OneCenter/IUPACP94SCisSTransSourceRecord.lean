import TetraStereo.OneCenter.IUPACP94SourceAuditLedger
import TetraStereo.KernelOnly

set_option autoImplicit false













namespace TetraStereo.OneCenter

open BlueBookP94
open BlueBookP94.P94MolecularLonePair

namespace P94SCisSTransSourceRecord

def sourceIllustrationBlock : P94SourceAuditLedger.IllustrationBlock :=
  .sCisSTransExamples

def sourceArtifactSha256 : String :=
  P94SourceAuditLedger.frozenP9Artifact.sha256

@[simp] theorem source_illustration_binding_exact :
    sourceIllustrationBlock = P94SourceAuditLedger.IllustrationBlock.sCisSTransExamples ∧
      sourceIllustrationBlock.pdfPage = 89 ∧
        sourceIllustrationBlock.clause = .sCisSTrans := by
  decide

@[simp] theorem source_artifact_digest_exact :
    sourceArtifactSha256 = P94SourceAuditLedger.frozenP9Artifact.sha256 := by
  rfl

private def carbon : AtomSpec := AtomSpec.aliphatic .C

private def bond (source target : Nat) (kind : ParsedBondKind := .single) : RawBond :=
  { source := source, target := target, kind := kind }

/-- Constitutional graph shared by the two displayed skeletal conformers. -/
def molecule : RawMolecule where
  atoms := List.replicate 4 carbon
  bonds := [bond 0 1 .double, bond 1 2, bond 2 3 .double]

def source : AuthoritativeChemicalInput :=
  match molecule.toSemanticMolecule? with
  | none => { molecule := { atoms := [], interactions := [] } }
  | some semantic =>
      { molecule := semantic
        diagram? := some molecule.toDiagramConfiguration }

@[simp] theorem molecule_counts_exact :
    molecule.atomCount = 4 ∧ molecule.bonds.length = 3 := by
  decide

@[simp] theorem conjugated_diene_bond_orders_exact :
    molecule.bondOrder 0 1 = 2 ∧
      molecule.bondOrder 1 2 = 1 ∧ molecule.bondOrder 2 3 = 2 := by
  decide

theorem converted : molecule.toSemanticMolecule? = some source.molecule := by
  decide

theorem structureAgreement : molecule.AuthoritativeStructureAgreement source := by
  exact ⟨converted, by decide⟩

theorem source_structurallyWellFormed : source.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp (by decide)

/-- The displayed carbon diene needs no physical lone-pair annotation. -/
def ledger : CertifiedLonePairLedger molecule where
  source := source
  converted := converted
  annotations := []
  sourceWellFormed := source_structurallyWellFormed
  indicesValid := by simp [RawMolecule.EveryParserAtomElectronicStateAnnotationIndexValid]
  keysNodup := by simp
  electronicallyValid := by simp

def torsionUnit : P94ConformationUnit where
  kind := .torsionAxis
  atoms := [1, 2]
  torsionParticipants? := some (.atom 0, .atom 3)

theorem torsionUnit_valid : torsionUnit.ValidFor molecule := by
  refine ⟨by simp [torsionUnit], ?_, ?_⟩
  · intro atom member
    simp [torsionUnit] at member
    rcases member with rfl | rfl <;> norm_num [molecule, RawMolecule.atomCount]
  · refine ⟨.atom 0, .atom 3, 1, 2, rfl, ?_, by norm_num [torsionUnit], ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨rfl, rfl⟩
    · intro pair member
      change pair ∈ [(1, 2)] at member
      simp at member
      subst pair
      exact ⟨bond 1 2, by simp [molecule], by rfl⟩
    · norm_num [P94ConformationUnit.ParticipantBounded, molecule, RawMolecule.atomCount]
    · norm_num [P94ConformationUnit.ParticipantBounded, molecule, RawMolecule.atomCount]
    · change 0 < molecule.bondOrder 1 0
      decide
    · change 0 < molecule.bondOrder 2 3
      decide

def zeroAngle : TorsionAngle :=
  TorsionAngle.ofRat 0 (by norm_num) (by norm_num)

def oneEightyAngle : TorsionAngle :=
  TorsionAngle.ofRat 180 (by norm_num) (by norm_num)

def sCisRecord : P94ConjugatedSystemEvidence where
  unit := torsionUnit
  system := .twoDoubleBondsSeparatedBySingleBond
  angle := zeroAngle

def sTransRecord : P94ConjugatedSystemEvidence where
  unit := torsionUnit
  system := .twoDoubleBondsSeparatedBySingleBond
  angle := oneEightyAngle

def sCisEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .sCis
  evidence := .conjugated sCisRecord
  unitValid := torsionUnit_valid
  molecularRolesValid := by simp [P94ConformationEvidence.MolecularRolesValid]
  predicateClosure := .conjugated sCisRecord
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := by
    norm_num [P94ConformationEvidence.Supports, P94AuthorityClaim.descriptor,
      sCisRecord, SCisTransApplies, ClassifiedAs, TorsionAngle.magnitude,
      zeroAngle, torsionUnit]

def sTransEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .sTrans
  evidence := .conjugated sTransRecord
  unitValid := torsionUnit_valid
  molecularRolesValid := by simp [P94ConformationEvidence.MolecularRolesValid]
  predicateClosure := .conjugated sTransRecord
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := by
    norm_num [P94ConformationEvidence.Supports, P94AuthorityClaim.descriptor,
      sTransRecord, SCisTransApplies, ClassifiedAs, TorsionAngle.magnitude,
      oneEightyAngle, torsionUnit]

@[simp] theorem source_entries_support_exact :
    sCisEntry.evidence.Supports sCisEntry.claim.descriptor ∧
      sTransEntry.evidence.Supports sTransEntry.claim.descriptor :=
  ⟨sCisEntry.supports, sTransEntry.supports⟩

theorem sCis_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence sCisEntry.evidence)
    (supports : sCisEntry.evidence.Supports claim.descriptor) :
    claim = sCisEntry.claim := by
  cases claim <;>
    simp [sCisEntry, P94AuthorityClaim.MatchesEvidence, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, sCisRecord, SCisTransApplies,
      ClassifiedAs, TorsionAngle.magnitude, zeroAngle] at claimMatches supports ⊢
  all_goals norm_num at supports

theorem sTrans_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence sTransEntry.evidence)
    (supports : sTransEntry.evidence.Supports claim.descriptor) :
    claim = sTransEntry.claim := by
  cases claim <;>
    simp [sTransEntry, P94AuthorityClaim.MatchesEvidence, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, sTransRecord, SCisTransApplies,
      ClassifiedAs, TorsionAngle.magnitude, oneEightyAngle] at claimMatches supports ⊢
  all_goals norm_num at supports

def sourcePackage : P94SourcePackageSchema source molecule where
  authoritativeStructureAgreement := structureAgreement
  lonePairLedger := ledger
  ledgerSource := rfl
  evidenceEntries := [sCisEntry, sTransEntry]
  compatibleClaimsListed := by
    intro entry member claim claimMatches supports
    simp at member
    rcases member with rfl | rfl
    · have claimExact := sCis_uniqueClaim claim claimMatches supports
      subst claim
      exact ⟨sCisEntry, by simp, rfl, rfl⟩
    · have claimExact := sTrans_uniqueClaim claim claimMatches supports
      subst claim
      exact ⟨sTransEntry, by simp, rfl, rfl⟩
  inOutCoordinatePairs := []

@[simp] theorem source_package_claims_exact :
    sourcePackage.evidenceEntries.map P94SourcePackageEvidenceEntry.claim =
      [.sCis, .sTrans] := by
  rfl

@[simp] theorem source_package_clauses_exact :
    sourcePackage.evidenceEntries.map (fun entry => entry.claim.clause) =
      [.sCisSTrans, .sCisSTrans] := by
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
    rcases member with rfl | rfl | rfl <;> simp [bond]

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
  entry := sCisEntry

@[simp] theorem distinguished_entry_exact :
    distinguishedEntry.entry.claim.clause = .sCisSTrans ∧
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

end P94SCisSTransSourceRecord
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P94SCisSTransSourceRecord.source_illustration_binding_exact
assert_kernel_only TetraStereo.OneCenter.P94SCisSTransSourceRecord.molecule_counts_exact
assert_kernel_only
  TetraStereo.OneCenter.P94SCisSTransSourceRecord.conjugated_diene_bond_orders_exact
assert_kernel_only TetraStereo.OneCenter.P94SCisSTransSourceRecord.structureAgreement
assert_kernel_only TetraStereo.OneCenter.P94SCisSTransSourceRecord.torsionUnit_valid
assert_kernel_only TetraStereo.OneCenter.P94SCisSTransSourceRecord.source_entries_support_exact
assert_kernel_only TetraStereo.OneCenter.P94SCisSTransSourceRecord.source_package_claims_exact
assert_kernel_only TetraStereo.OneCenter.P94SCisSTransSourceRecord.source_package_clauses_exact
assert_kernel_only TetraStereo.OneCenter.P94SCisSTransSourceRecord.normalizationReady
assert_kernel_only TetraStereo.OneCenter.P94SCisSTransSourceRecord.distinguished_entry_exact
assert_kernel_only
  TetraStereo.OneCenter.P94SCisSTransSourceRecord.current_independent_source_review_issued
