import TetraStereo.OneCenter.IUPACP94SourceAuditLedger
import TetraStereo.KernelOnly

set_option autoImplicit false














namespace TetraStereo.OneCenter

open BlueBookP94
open BlueBookP94.P94MolecularLonePair

namespace P94HalfChairSourceRecord

def sourceIllustrationBlock : P94SourceAuditLedger.IllustrationBlock :=
  .halfChairExample

def sourceArtifactSha256 : String :=
  P94SourceAuditLedger.frozenP9Artifact.sha256

@[simp] theorem source_illustration_binding_exact :
    sourceIllustrationBlock = P94SourceAuditLedger.IllustrationBlock.halfChairExample ∧
      sourceIllustrationBlock.pdfPage = 90 ∧
        sourceIllustrationBlock.clause = .halfChair := by
  decide

@[simp] theorem source_artifact_digest_exact :
    sourceArtifactSha256 = P94SourceAuditLedger.frozenP9Artifact.sha256 := by
  rfl

private def carbon : AtomSpec := AtomSpec.aliphatic .C

private def bond (source target : Nat) (kind : ParsedBondKind := .single) : RawBond :=
  { source := source, target := target, kind := kind }

/-- Closed six-carbon ring with the single double bond drawn in the half-chair example. -/
def molecule : RawMolecule where
  atoms := List.replicate 6 carbon
  bonds :=
    [bond 0 1 .double, bond 1 2, bond 2 3,
      bond 3 4, bond 4 5, bond 5 0]

def source : AuthoritativeChemicalInput :=
  match molecule.toSemanticMolecule? with
  | none => { molecule := { atoms := [], interactions := [] } }
  | some semantic =>
      { molecule := semantic
        diagram? := some molecule.toDiagramConfiguration }

@[simp] theorem molecule_counts_exact :
    molecule.atomCount = 6 ∧ molecule.bonds.length = 6 := by
  decide

def ringUnit : P94ConformationUnit where
  kind := .sixMemberedRing
  atoms := [0, 1, 2, 3, 4, 5]

@[simp] theorem six_ring_bond_orders_exact :
    ringUnit.cycleBondOrders molecule = [2, 1, 1, 1, 1, 1] := by
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

theorem monounsaturated_ring_exact :
    ringUnit.CycleDoubleBondCount molecule = 1 ∧
      ringUnit.MonounsaturatedCyclic molecule := by
  have count : ringUnit.CycleDoubleBondCount molecule = 1 := by
    simp [P94ConformationUnit.CycleDoubleBondCount, six_ring_bond_orders_exact]
  refine ⟨count, count, ?_⟩
  intro edge edgeMember rawBond rawBondMember _connects
  have allowed : rawBond.kind = .single ∨ rawBond.kind = .double := by
    simp [molecule, bond] at rawBondMember
    rcases rawBondMember with h | h | h | h | h | h <;> subst rawBond <;> simp
  rcases allowed with allowed | allowed <;> rw [allowed] <;>
    simp [P94ConformationUnit.MonounsaturatedCycleBondKind]

def halfChairObservation : HalfChairObservation where
  ringSize := 6
  doubleBondCount := 1
  firstRemoteSide := .positive
  secondRemoteSide := .negative

@[simp] theorem half_chair_observation_exact :
    halfChairObservation.ringSize = 6 ∧
      halfChairObservation.doubleBondCount = 1 ∧
        OppositeSides halfChairObservation.firstRemoteSide
          halfChairObservation.secondRemoteSide := by
  simp [halfChairObservation, OppositeSides]

def halfChairRecord : P94HalfChairEvidence where
  unit := ringUnit
  observation := halfChairObservation

theorem halfChair_roles :
    (P94ConformationEvidence.halfChair halfChairRecord : P94ReviewedEvidence).MolecularRolesValid
      molecule := by
  change halfChairObservation.doubleBondCount = ringUnit.CycleDoubleBondCount molecule ∧
    ringUnit.MonounsaturatedCyclic molecule
  exact
    ⟨by simpa [halfChairObservation] using monounsaturated_ring_exact.1.symm,
      monounsaturated_ring_exact.2⟩

def halfChairEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .halfChair
  evidence := .halfChair halfChairRecord
  unitValid := ringUnit_valid
  molecularRolesValid := halfChair_roles
  predicateClosure := .halfChair halfChairRecord
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := by
    simp [P94ConformationEvidence.Supports, P94AuthorityClaim.descriptor,
      halfChairRecord, halfChairObservation, ringUnit, IsHalfChair, OppositeSides]

@[simp] theorem source_entry_support_exact :
    halfChairEntry.evidence.Supports halfChairEntry.claim.descriptor :=
  halfChairEntry.supports

theorem halfChair_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence halfChairEntry.evidence)
    (supports : halfChairEntry.evidence.Supports claim.descriptor) :
    claim = halfChairEntry.claim := by
  cases claim <;>
    simp [halfChairEntry, P94AuthorityClaim.MatchesEvidence] at claimMatches ⊢

def sourcePackage : P94SourcePackageSchema source molecule where
  authoritativeStructureAgreement := structureAgreement
  lonePairLedger := ledger
  ledgerSource := rfl
  evidenceEntries := [halfChairEntry]
  compatibleClaimsListed := by
    intro entry member claim claimMatches supports
    simp at member
    subst entry
    have claimExact := halfChair_uniqueClaim claim claimMatches supports
    subst claim
    exact ⟨halfChairEntry, by simp, rfl, rfl⟩
  inOutCoordinatePairs := []

@[simp] theorem source_package_claims_exact :
    sourcePackage.evidenceEntries.map P94SourcePackageEvidenceEntry.claim = [.halfChair] := by
  rfl

@[simp] theorem source_package_clauses_exact :
    sourcePackage.evidenceEntries.map (fun entry => entry.claim.clause) = [.halfChair] := by
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
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [bond]

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
  entry := halfChairEntry

@[simp] theorem distinguished_entry_exact :
    distinguishedEntry.entry.claim.clause = .halfChair ∧
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

end P94HalfChairSourceRecord
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P94HalfChairSourceRecord.source_illustration_binding_exact
assert_kernel_only TetraStereo.OneCenter.P94HalfChairSourceRecord.molecule_counts_exact
assert_kernel_only TetraStereo.OneCenter.P94HalfChairSourceRecord.six_ring_bond_orders_exact
assert_kernel_only TetraStereo.OneCenter.P94HalfChairSourceRecord.structureAgreement
assert_kernel_only TetraStereo.OneCenter.P94HalfChairSourceRecord.ringUnit_valid
assert_kernel_only TetraStereo.OneCenter.P94HalfChairSourceRecord.monounsaturated_ring_exact
assert_kernel_only TetraStereo.OneCenter.P94HalfChairSourceRecord.half_chair_observation_exact
assert_kernel_only TetraStereo.OneCenter.P94HalfChairSourceRecord.halfChair_roles
assert_kernel_only TetraStereo.OneCenter.P94HalfChairSourceRecord.source_entry_support_exact
assert_kernel_only TetraStereo.OneCenter.P94HalfChairSourceRecord.source_package_claims_exact
assert_kernel_only TetraStereo.OneCenter.P94HalfChairSourceRecord.source_package_clauses_exact
assert_kernel_only TetraStereo.OneCenter.P94HalfChairSourceRecord.normalizationReady
assert_kernel_only TetraStereo.OneCenter.P94HalfChairSourceRecord.distinguished_entry_exact
assert_kernel_only
  TetraStereo.OneCenter.P94HalfChairSourceRecord.current_independent_source_review_issued
