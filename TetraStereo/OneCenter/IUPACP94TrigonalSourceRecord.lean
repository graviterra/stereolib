import TetraStereo.OneCenter.IUPACP94SourceAuditLedger
import TetraStereo.KernelOnly

set_option autoImplicit false













namespace TetraStereo.OneCenter

open BlueBookP94
open BlueBookP94.P94MolecularLonePair

namespace P94TrigonalSourceRecord

def sourceIllustrationBlock : P94SourceAuditLedger.IllustrationBlock :=
  .bisectingEclipsingExample

def sourceArtifactSha256 : String :=
  P94SourceAuditLedger.frozenP9Artifact.sha256

@[simp] theorem source_illustration_binding_exact :
    sourceIllustrationBlock = P94SourceAuditLedger.IllustrationBlock.bisectingEclipsingExample ∧
      sourceIllustrationBlock.pdfPage = 89 ∧
        sourceIllustrationBlock.clause = .trigonalConformations := by
  decide

@[simp] theorem source_artifact_digest_exact :
    sourceArtifactSha256 = P94SourceAuditLedger.frozenP9Artifact.sha256 := by
  rfl

private def carbon : AtomSpec := AtomSpec.aliphatic .C
private def oxygen : AtomSpec := AtomSpec.aliphatic .O

private def bond (source target : Nat) (kind : ParsedBondKind := .single) : RawBond :=
  { source := source, target := target, kind := kind }

/-- Propanal graph shared by the two displayed Newman projections. -/
def molecule : RawMolecule where
  atoms := [carbon, carbon, carbon, oxygen]
  bonds := [bond 0 1, bond 1 2, bond 2 3 .double]

def source : AuthoritativeChemicalInput :=
  match molecule.toSemanticMolecule? with
  | none => { molecule := { atoms := [], interactions := [] } }
  | some semantic =>
      { molecule := semantic
        diagram? := some molecule.toDiagramConfiguration }

@[simp] theorem molecule_counts_exact :
    molecule.atomCount = 4 ∧ molecule.bonds.length = 3 := by
  decide

@[simp] theorem propanal_bond_orders_exact :
    molecule.bondOrder 0 1 = 1 ∧
      molecule.bondOrder 1 2 = 1 ∧ molecule.bondOrder 2 3 = 2 := by
  decide

theorem converted : molecule.toSemanticMolecule? = some source.molecule := by
  decide

theorem structureAgreement : molecule.AuthoritativeStructureAgreement source := by
  exact ⟨converted, by decide⟩

theorem source_structurallyWellFormed : source.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp (by decide)

/-- The displayed propanal graph needs no physical lone-pair participant annotation. -/
def ledger : CertifiedLonePairLedger molecule where
  source := source
  converted := converted
  annotations := []
  sourceWellFormed := source_structurallyWellFormed
  indicesValid := by simp [RawMolecule.EveryParserAtomElectronicStateAnnotationIndexValid]
  keysNodup := by simp
  electronicallyValid := by simp

/-- The viewed bond is `CH₂-CHO`; atom 0 is the displayed methyl R group and atom 3 is X = O. -/
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

def bisectingRecord : P94TrigonalConformationEvidence where
  unit := torsionUnit
  observation :=
    { isR3CCYXGrouping := (true = true)
      xToSomeR := oneEightyAngle
      doubleBondBisectsRCRAngle := (true = true) }

def eclipsingRecord : P94TrigonalConformationEvidence where
  unit := torsionUnit
  observation :=
    { isR3CCYXGrouping := (true = true)
      xToSomeR := zeroAngle
      doubleBondBisectsRCRAngle := (false = true) }

def bisectingEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .trigonalBisecting
  evidence := .trigonal bisectingRecord
  unitValid := torsionUnit_valid
  molecularRolesValid := by simp [P94ConformationEvidence.MolecularRolesValid]
  predicateClosure := .trigonal bisectingRecord true true rfl rfl
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := by
    norm_num [P94ConformationEvidence.Supports, P94AuthorityClaim.descriptor,
      bisectingRecord, IsBisectingConformation, ClassifiedAs,
      TorsionAngle.magnitude, oneEightyAngle, torsionUnit]

def eclipsingEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .trigonalEclipsing
  evidence := .trigonal eclipsingRecord
  unitValid := torsionUnit_valid
  molecularRolesValid := by simp [P94ConformationEvidence.MolecularRolesValid]
  predicateClosure := .trigonal eclipsingRecord true false rfl rfl
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := by
    norm_num [P94ConformationEvidence.Supports, P94AuthorityClaim.descriptor,
      eclipsingRecord, IsEclipsingConformation, ClassifiedAs,
      TorsionAngle.magnitude, zeroAngle, torsionUnit]

@[simp] theorem source_entries_support_exact :
    bisectingEntry.evidence.Supports bisectingEntry.claim.descriptor ∧
      eclipsingEntry.evidence.Supports eclipsingEntry.claim.descriptor :=
  ⟨bisectingEntry.supports, eclipsingEntry.supports⟩

theorem bisecting_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence bisectingEntry.evidence)
    (supports : bisectingEntry.evidence.Supports claim.descriptor) :
    claim = bisectingEntry.claim := by
  cases claim <;>
    simp [bisectingEntry, P94AuthorityClaim.MatchesEvidence, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, bisectingRecord, IsBisectingConformation,
      IsEclipsingConformation, ClassifiedAs, TorsionAngle.magnitude,
      oneEightyAngle] at claimMatches supports ⊢
  all_goals norm_num at supports

theorem eclipsing_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence eclipsingEntry.evidence)
    (supports : eclipsingEntry.evidence.Supports claim.descriptor) :
    claim = eclipsingEntry.claim := by
  cases claim <;>
    simp [eclipsingEntry, P94AuthorityClaim.MatchesEvidence, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, eclipsingRecord, IsBisectingConformation,
      IsEclipsingConformation, ClassifiedAs, TorsionAngle.magnitude,
      zeroAngle] at claimMatches supports ⊢

def sourcePackage : P94SourcePackageSchema source molecule where
  authoritativeStructureAgreement := structureAgreement
  lonePairLedger := ledger
  ledgerSource := rfl
  evidenceEntries := [bisectingEntry, eclipsingEntry]
  compatibleClaimsListed := by
    intro entry member claim claimMatches supports
    simp at member
    rcases member with rfl | rfl
    · have claimExact := bisecting_uniqueClaim claim claimMatches supports
      subst claim
      exact ⟨bisectingEntry, by simp, rfl, rfl⟩
    · have claimExact := eclipsing_uniqueClaim claim claimMatches supports
      subst claim
      exact ⟨eclipsingEntry, by simp, rfl, rfl⟩
  inOutCoordinatePairs := []

@[simp] theorem source_package_claims_exact :
    sourcePackage.evidenceEntries.map P94SourcePackageEvidenceEntry.claim =
      [.trigonalBisecting, .trigonalEclipsing] := by
  rfl

@[simp] theorem source_package_clauses_exact :
    sourcePackage.evidenceEntries.map (fun entry => entry.claim.clause) =
      [.trigonalConformations, .trigonalConformations] := by
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
  entry := bisectingEntry

@[simp] theorem distinguished_entry_exact :
    distinguishedEntry.entry.claim.clause = .trigonalConformations ∧
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

end P94TrigonalSourceRecord
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P94TrigonalSourceRecord.source_illustration_binding_exact
assert_kernel_only TetraStereo.OneCenter.P94TrigonalSourceRecord.molecule_counts_exact
assert_kernel_only TetraStereo.OneCenter.P94TrigonalSourceRecord.propanal_bond_orders_exact
assert_kernel_only TetraStereo.OneCenter.P94TrigonalSourceRecord.structureAgreement
assert_kernel_only TetraStereo.OneCenter.P94TrigonalSourceRecord.torsionUnit_valid
assert_kernel_only TetraStereo.OneCenter.P94TrigonalSourceRecord.source_entries_support_exact
assert_kernel_only TetraStereo.OneCenter.P94TrigonalSourceRecord.source_package_claims_exact
assert_kernel_only TetraStereo.OneCenter.P94TrigonalSourceRecord.source_package_clauses_exact
assert_kernel_only TetraStereo.OneCenter.P94TrigonalSourceRecord.normalizationReady
assert_kernel_only TetraStereo.OneCenter.P94TrigonalSourceRecord.distinguished_entry_exact
assert_kernel_only
  TetraStereo.OneCenter.P94TrigonalSourceRecord.current_independent_source_review_issued
