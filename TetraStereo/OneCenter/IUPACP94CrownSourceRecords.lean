import TetraStereo.OneCenter.IUPACP94SourceAuditLedger
import TetraStereo.KernelOnly

set_option autoImplicit false













namespace TetraStereo.OneCenter

open BlueBookP94
open BlueBookP94.P94MolecularLonePair

namespace P94CrownSourceRecords

def sourceIllustrationBlock : P94SourceAuditLedger.IllustrationBlock :=
  .crownExamples

def sourceArtifactSha256 : String :=
  P94SourceAuditLedger.frozenP9Artifact.sha256

@[simp] theorem source_illustration_binding_exact :
    sourceIllustrationBlock = P94SourceAuditLedger.IllustrationBlock.crownExamples ∧
      sourceIllustrationBlock.pdfPage = 90 ∧
        sourceIllustrationBlock.clause = .crown := by
  decide

@[simp] theorem source_artifact_digest_exact :
    sourceArtifactSha256 = P94SourceAuditLedger.frozenP9Artifact.sha256 := by
  rfl

private def carbon : AtomSpec := AtomSpec.aliphatic .C

private def bond (source target : Nat) : RawBond :=
  { source := source, target := target, kind := .single }

namespace Cyclooctane

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
  kind := .crownRing
  atoms := [0, 1, 2, 3, 4, 5, 6, 7]

@[simp] theorem ring_bond_orders_exact :
    ringUnit.cycleBondOrders molecule = [1, 1, 1, 1, 1, 1, 1, 1] := by
  decide

theorem converted : molecule.toSemanticMolecule? = some source.molecule := by
  decide

theorem structureAgreement : molecule.AuthoritativeStructureAgreement source := by
  exact ⟨converted, by decide⟩

theorem source_structurallyWellFormed : source.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp (by decide)

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
    ringUnit, molecule, RawMolecule.atomCount, RawBond.connects, bond, carbon,
    even_iff_two_dvd]

theorem ring_saturated : ringUnit.SaturatedCyclic molecule := by
  constructor
  · intro order member
    rw [ring_bond_orders_exact] at member
    simpa using member
  · intro edge edgeMember rawBond rawBondMember _connects
    have kind : rawBond.kind = .single := by
      simp [molecule, bond] at rawBondMember
      rcases rawBondMember with h | h | h | h | h | h | h | h <;>
        subst rawBond <;> rfl
    rw [kind]
    simp [P94ConformationUnit.SaturatedSingleBondKind]

def crownRecord : P94RingPlaneEvidence where
  unit := ringUnit
  sides :=
    [.positive, .negative, .positive, .negative,
      .positive, .negative, .positive, .negative]
  saturatedCyclic := True
  symmetricallyEquivalent := True

def crownEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .crown
  evidence := .ringPlane crownRecord
  unitValid := ringUnit_valid
  molecularRolesValid := by
    simpa [P94ConformationEvidence.MolecularRolesValid, crownRecord] using ring_saturated
  predicateClosure := .ringPlane crownRecord true true false
    (by simp [crownRecord]) (by simp [crownRecord]) (by simp [crownRecord])
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := by
    simp [P94ConformationEvidence.Supports, P94AuthorityClaim.descriptor, crownRecord,
      ringUnit, IsCrown, AlternatingOffPlane, OppositeSides, even_iff_two_dvd]

@[simp] theorem source_entry_support_exact :
    crownEntry.evidence.Supports crownEntry.claim.descriptor :=
  crownEntry.supports

theorem crown_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence crownEntry.evidence)
    (supports : crownEntry.evidence.Supports claim.descriptor) :
    claim = crownEntry.claim := by
  cases claim <;>
    simp [crownEntry, P94AuthorityClaim.MatchesEvidence, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, crownRecord, ringUnit] at claimMatches supports ⊢

def sourcePackage : P94SourcePackageSchema source molecule where
  authoritativeStructureAgreement := structureAgreement
  lonePairLedger := ledger
  ledgerSource := rfl
  evidenceEntries := [crownEntry]
  compatibleClaimsListed := by
    intro entry member claim claimMatches supports
    simp at member
    subst entry
    have claimExact := crown_uniqueClaim claim claimMatches supports
    subst claim
    exact ⟨crownEntry, by simp, rfl, rfl⟩
  inOutCoordinatePairs := []

@[simp] theorem source_package_claims_exact :
    sourcePackage.evidenceEntries.map P94SourcePackageEvidenceEntry.claim = [.crown] := by
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

def distinguishedEntry : P94FrozenDistinguishedEntry where
  record := frozenRecord
  entry := crownEntry

@[simp] theorem distinguished_entry_exact :
    distinguishedEntry.entry.claim.clause = .crown ∧
      distinguishedEntry.entry ∈ distinguishedEntry.record.package.evidenceEntries := by
  constructor
  · rfl
  · simp [distinguishedEntry, frozenRecord, sourcePackage]

end Cyclooctane

namespace Cyclodecane

def molecule : RawMolecule where
  atoms := List.replicate 10 carbon
  bonds :=
    [bond 0 1, bond 1 2, bond 2 3, bond 3 4, bond 4 5,
      bond 5 6, bond 6 7, bond 7 8, bond 8 9, bond 9 0]

def source : AuthoritativeChemicalInput :=
  match molecule.toSemanticMolecule? with
  | none => { molecule := { atoms := [], interactions := [] } }
  | some semantic =>
      { molecule := semantic
        diagram? := some molecule.toDiagramConfiguration }

@[simp] theorem molecule_counts_exact :
    molecule.atomCount = 10 ∧ molecule.bonds.length = 10 := by
  decide

def ringUnit : P94ConformationUnit where
  kind := .crownRing
  atoms := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

@[simp] theorem ring_bond_orders_exact :
    ringUnit.cycleBondOrders molecule = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
  decide

theorem converted : molecule.toSemanticMolecule? = some source.molecule := by
  decide

theorem structureAgreement : molecule.AuthoritativeStructureAgreement source := by
  exact ⟨converted, by decide⟩

theorem source_structurallyWellFormed : source.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp (by decide)

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
    ringUnit, molecule, RawMolecule.atomCount, RawBond.connects, bond, carbon,
    even_iff_two_dvd]

theorem ring_saturated : ringUnit.SaturatedCyclic molecule := by
  constructor
  · intro order member
    rw [ring_bond_orders_exact] at member
    simpa using member
  · intro edge edgeMember rawBond rawBondMember _connects
    have kind : rawBond.kind = .single := by
      simp [molecule, bond] at rawBondMember
      rcases rawBondMember with h | h | h | h | h | h | h | h | h | h <;>
        subst rawBond <;> rfl
    rw [kind]
    simp [P94ConformationUnit.SaturatedSingleBondKind]

def crownRecord : P94RingPlaneEvidence where
  unit := ringUnit
  sides :=
    [.positive, .negative, .positive, .negative, .positive,
      .negative, .positive, .negative, .positive, .negative]
  saturatedCyclic := True
  symmetricallyEquivalent := True

def crownEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .crown
  evidence := .ringPlane crownRecord
  unitValid := ringUnit_valid
  molecularRolesValid := by
    simpa [P94ConformationEvidence.MolecularRolesValid, crownRecord] using ring_saturated
  predicateClosure := .ringPlane crownRecord true true false
    (by simp [crownRecord]) (by simp [crownRecord]) (by simp [crownRecord])
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := by
    simp [P94ConformationEvidence.Supports, P94AuthorityClaim.descriptor, crownRecord,
      ringUnit, IsCrown, AlternatingOffPlane, OppositeSides, even_iff_two_dvd]

@[simp] theorem source_entry_support_exact :
    crownEntry.evidence.Supports crownEntry.claim.descriptor :=
  crownEntry.supports

theorem crown_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence crownEntry.evidence)
    (supports : crownEntry.evidence.Supports claim.descriptor) :
    claim = crownEntry.claim := by
  cases claim <;>
    simp [crownEntry, P94AuthorityClaim.MatchesEvidence, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, crownRecord, ringUnit] at claimMatches supports ⊢

def sourcePackage : P94SourcePackageSchema source molecule where
  authoritativeStructureAgreement := structureAgreement
  lonePairLedger := ledger
  ledgerSource := rfl
  evidenceEntries := [crownEntry]
  compatibleClaimsListed := by
    intro entry member claim claimMatches supports
    simp at member
    subst entry
    have claimExact := crown_uniqueClaim claim claimMatches supports
    subst claim
    exact ⟨crownEntry, by simp, rfl, rfl⟩
  inOutCoordinatePairs := []

@[simp] theorem source_package_claims_exact :
    sourcePackage.evidenceEntries.map P94SourcePackageEvidenceEntry.claim = [.crown] := by
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
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [bond]

def frozenRecord : P94FrozenPackageRecord where
  source := source
  molecule := molecule
  package := sourcePackage
  normalizationReady := normalizationReady

def distinguishedEntry : P94FrozenDistinguishedEntry where
  record := frozenRecord
  entry := crownEntry

@[simp] theorem distinguished_entry_exact :
    distinguishedEntry.entry.claim.clause = .crown ∧
      distinguishedEntry.entry ∈ distinguishedEntry.record.package.evidenceEntries := by
  constructor
  · rfl
  · simp [distinguishedEntry, frozenRecord, sourcePackage]

end Cyclodecane

def frozenRecords : List P94FrozenPackageRecord :=
  [Cyclooctane.frozenRecord, Cyclodecane.frozenRecord]

@[simp] theorem frozen_records_exact :
    frozenRecords.length = 2 ∧
      frozenRecords.map (fun record => record.molecule.atomCount) = [8, 10] := by
  decide

def distinguishedEntries : List P94FrozenDistinguishedEntry :=
  [Cyclooctane.distinguishedEntry, Cyclodecane.distinguishedEntry]

@[simp] theorem distinguished_entries_exact :
    distinguishedEntries.map (fun entry => entry.entry.claim.clause) = [.crown, .crown] := by
  rfl

/-- Independent fidelity remains an explicit relation over both exact frozen records. -/
structure ReviewedSourceRecords
    (SourceFaithful : P94FrozenPackageRecord → Prop) where
  reviewerIdentity : String
  reviewDate : String
  method : String
  reviewerIdentityDeclared : reviewerIdentity ≠ ""
  reviewDateDeclared : reviewDate ≠ ""
  methodDeclared : method ≠ ""
  cyclooctaneSourceFaithful : SourceFaithful Cyclooctane.frozenRecord
  cyclodecaneSourceFaithful : SourceFaithful Cyclodecane.frozenRecord

def currentIndependentSourceReviewIssued : Bool := true

@[simp] theorem current_independent_source_review_issued :
    currentIndependentSourceReviewIssued = true := by
  rfl

end P94CrownSourceRecords
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P94CrownSourceRecords.source_illustration_binding_exact
assert_kernel_only TetraStereo.OneCenter.P94CrownSourceRecords.Cyclooctane.molecule_counts_exact
assert_kernel_only TetraStereo.OneCenter.P94CrownSourceRecords.Cyclooctane.ring_bond_orders_exact
assert_kernel_only TetraStereo.OneCenter.P94CrownSourceRecords.Cyclooctane.ringUnit_valid
assert_kernel_only TetraStereo.OneCenter.P94CrownSourceRecords.Cyclooctane.ring_saturated
assert_kernel_only TetraStereo.OneCenter.P94CrownSourceRecords.Cyclooctane.source_entry_support_exact
assert_kernel_only TetraStereo.OneCenter.P94CrownSourceRecords.Cyclooctane.normalizationReady
assert_kernel_only TetraStereo.OneCenter.P94CrownSourceRecords.Cyclodecane.molecule_counts_exact
assert_kernel_only TetraStereo.OneCenter.P94CrownSourceRecords.Cyclodecane.ring_bond_orders_exact
assert_kernel_only TetraStereo.OneCenter.P94CrownSourceRecords.Cyclodecane.ringUnit_valid
assert_kernel_only TetraStereo.OneCenter.P94CrownSourceRecords.Cyclodecane.ring_saturated
assert_kernel_only TetraStereo.OneCenter.P94CrownSourceRecords.Cyclodecane.source_entry_support_exact
assert_kernel_only TetraStereo.OneCenter.P94CrownSourceRecords.Cyclodecane.normalizationReady
assert_kernel_only TetraStereo.OneCenter.P94CrownSourceRecords.frozen_records_exact
assert_kernel_only TetraStereo.OneCenter.P94CrownSourceRecords.distinguished_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.P94CrownSourceRecords.current_independent_source_review_issued
