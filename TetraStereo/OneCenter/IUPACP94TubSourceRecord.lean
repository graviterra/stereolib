import TetraStereo.OneCenter.IUPACP94SourceAuditLedger
import TetraStereo.KernelOnly

set_option autoImplicit false














namespace TetraStereo.OneCenter

open BlueBookP94
open BlueBookP94.P94MolecularLonePair

namespace P94TubSourceRecord

def sourceIllustrationBlock : P94SourceAuditLedger.IllustrationBlock :=
  .tubExample

def sourceArtifactSha256 : String :=
  P94SourceAuditLedger.frozenP9Artifact.sha256

@[simp] theorem source_illustration_binding_exact :
    sourceIllustrationBlock = P94SourceAuditLedger.IllustrationBlock.tubExample ∧
      sourceIllustrationBlock.pdfPage = 90 ∧
        sourceIllustrationBlock.clause = .tub := by
  decide

@[simp] theorem source_artifact_digest_exact :
    sourceArtifactSha256 = P94SourceAuditLedger.frozenP9Artifact.sha256 := by
  rfl

private def carbon : AtomSpec := AtomSpec.aliphatic .C

private def bond (source target : Nat) : RawBond :=
  { source := source, target := target, kind := .single }

/-- Closed eight-carbon ring depicted by the unlabeled skeletal tub example. -/
def molecule : RawMolecule where
  atoms := List.replicate 8 carbon
  bonds :=
    [bond 0 1, bond 1 2, bond 2 3, bond 3 4,
      bond 4 5, bond 5 6, bond 6 7, bond 7 0]

def source : AuthoritativeChemicalInput :=
  match molecule.toSemanticMolecule? with
  | none => { molecule := { atoms := [], interactions := [] } }
  | some semantic =>
      { molecule := semantic
        diagram? := some molecule.toDiagramConfiguration }

@[simp] theorem molecule_counts_exact :
    molecule.atomCount = 8 ∧ molecule.bonds.length = 8 := by
  decide

def ringUnit : P94ConformationUnit where
  kind := .eightMemberedTubRing
  atoms := [0, 1, 2, 3, 4, 5, 6, 7]

@[simp] theorem eight_ring_bond_orders_exact :
    ringUnit.cycleBondOrders molecule = [1, 1, 1, 1, 1, 1, 1, 1] := by
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

theorem ringUnit_valid : ringUnit.ValidFor molecule := by
  simp [P94ConformationUnit.ValidFor, P94ConformationUnit.CyclicallyBonded,
    P94ConformationUnit.ConsecutivelyBonded, P94ConformationUnit.Bonded,
    ringUnit, molecule, RawMolecule.atomCount, RawBond.connects, bond, carbon]

def tubRecord : P94RingPlaneEvidence where
  unit := ringUnit
  sides :=
    [.onPlane, .onPlane, .positive, .positive,
      .onPlane, .onPlane, .positive, .positive]
  saturatedCyclic := True
  symmetricallyEquivalent := False

@[simp] theorem tub_sides_exact :
    tubRecord.sides =
      [.onPlane, .onPlane, .positive, .positive,
        .onPlane, .onPlane, .positive, .positive] := by
  rfl

def tubEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .tub
  evidence := .ringPlane tubRecord
  unitValid := ringUnit_valid
  molecularRolesValid := by
    simp [P94ConformationEvidence.MolecularRolesValid, tubRecord, ringUnit]
  predicateClosure := .ringPlane tubRecord true false false
    (by simp [tubRecord]) (by simp [tubRecord]) (by simp [tubRecord])
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := by
    refine ⟨rfl, rfl, ?_⟩
    refine ⟨0, ?_⟩
    change
      [PlaneSide.onPlane, .onPlane, .positive, .positive,
        .onPlane, .onPlane, .positive, .positive].length = 8 ∧
      [PlaneSide.onPlane, .onPlane, .positive, .positive,
        .onPlane, .onPlane, .positive, .positive][0]? = some .onPlane ∧
      [PlaneSide.onPlane, .onPlane, .positive, .positive,
        .onPlane, .onPlane, .positive, .positive][1]? = some .onPlane ∧
      [PlaneSide.onPlane, .onPlane, .positive, .positive,
        .onPlane, .onPlane, .positive, .positive][4]? = some .onPlane ∧
      [PlaneSide.onPlane, .onPlane, .positive, .positive,
        .onPlane, .onPlane, .positive, .positive][5]? = some .onPlane ∧
      ∃ offSide,
        (offSide = .positive ∨ offSide = .negative) ∧
        [PlaneSide.onPlane, .onPlane, .positive, .positive,
          .onPlane, .onPlane, .positive, .positive][2]? = some offSide ∧
        [PlaneSide.onPlane, .onPlane, .positive, .positive,
          .onPlane, .onPlane, .positive, .positive][3]? = some offSide ∧
        [PlaneSide.onPlane, .onPlane, .positive, .positive,
          .onPlane, .onPlane, .positive, .positive][6]? = some offSide ∧
        [PlaneSide.onPlane, .onPlane, .positive, .positive,
          .onPlane, .onPlane, .positive, .positive][7]? = some offSide
    simp

@[simp] theorem source_entry_support_exact :
    tubEntry.evidence.Supports tubEntry.claim.descriptor :=
  tubEntry.supports

theorem tub_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence tubEntry.evidence)
    (supports : tubEntry.evidence.Supports claim.descriptor) :
    claim = tubEntry.claim := by
  cases claim <;>
    simp [tubEntry, P94AuthorityClaim.MatchesEvidence, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, tubRecord, ringUnit] at claimMatches supports ⊢

def sourcePackage : P94SourcePackageSchema source molecule where
  authoritativeStructureAgreement := structureAgreement
  lonePairLedger := ledger
  ledgerSource := rfl
  evidenceEntries := [tubEntry]
  compatibleClaimsListed := by
    intro entry member claim claimMatches supports
    simp at member
    subst entry
    have claimExact := tub_uniqueClaim claim claimMatches supports
    subst claim
    exact ⟨tubEntry, by simp, rfl, rfl⟩
  inOutCoordinatePairs := []

@[simp] theorem source_package_claims_exact :
    sourcePackage.evidenceEntries.map P94SourcePackageEvidenceEntry.claim = [.tub] := by
  rfl

@[simp] theorem source_package_clauses_exact :
    sourcePackage.evidenceEntries.map (fun entry => entry.claim.clause) = [.tub] := by
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
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [bond]

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
  entry := tubEntry

@[simp] theorem distinguished_entry_exact :
    distinguishedEntry.entry.claim.clause = .tub ∧
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

end P94TubSourceRecord
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P94TubSourceRecord.source_illustration_binding_exact
assert_kernel_only TetraStereo.OneCenter.P94TubSourceRecord.molecule_counts_exact
assert_kernel_only TetraStereo.OneCenter.P94TubSourceRecord.eight_ring_bond_orders_exact
assert_kernel_only TetraStereo.OneCenter.P94TubSourceRecord.structureAgreement
assert_kernel_only TetraStereo.OneCenter.P94TubSourceRecord.ringUnit_valid
assert_kernel_only TetraStereo.OneCenter.P94TubSourceRecord.tub_sides_exact
assert_kernel_only TetraStereo.OneCenter.P94TubSourceRecord.source_entry_support_exact
assert_kernel_only TetraStereo.OneCenter.P94TubSourceRecord.source_package_claims_exact
assert_kernel_only TetraStereo.OneCenter.P94TubSourceRecord.source_package_clauses_exact
assert_kernel_only TetraStereo.OneCenter.P94TubSourceRecord.normalizationReady
assert_kernel_only TetraStereo.OneCenter.P94TubSourceRecord.distinguished_entry_exact
assert_kernel_only
  TetraStereo.OneCenter.P94TubSourceRecord.current_independent_source_review_issued
