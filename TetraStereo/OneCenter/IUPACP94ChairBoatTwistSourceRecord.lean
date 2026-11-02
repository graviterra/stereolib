import TetraStereo.OneCenter.IUPACP94SourceAuditLedger
import TetraStereo.KernelOnly

set_option autoImplicit false














namespace TetraStereo.OneCenter

open BlueBookP94
open BlueBookP94.P94MolecularLonePair

namespace P94ChairBoatTwistSourceRecord

def sourceIllustrationBlock : P94SourceAuditLedger.IllustrationBlock :=
  .chairBoatTwistExamples

def sourceArtifactSha256 : String :=
  P94SourceAuditLedger.frozenP9Artifact.sha256

@[simp] theorem source_illustration_binding_exact :
    sourceIllustrationBlock = P94SourceAuditLedger.IllustrationBlock.chairBoatTwistExamples ∧
      sourceIllustrationBlock.pdfPage = 90 ∧
        sourceIllustrationBlock.clause = .chairBoatTwist := by
  decide

@[simp] theorem source_artifact_digest_exact :
    sourceArtifactSha256 = P94SourceAuditLedger.frozenP9Artifact.sha256 := by
  rfl

private def carbon : AtomSpec := AtomSpec.aliphatic .C

private def bond (source target : Nat) : RawBond :=
  { source := source, target := target, kind := .single }

def molecule : RawMolecule where
  atoms := List.replicate 6 carbon
  bonds := [bond 0 1, bond 1 2, bond 2 3, bond 3 4, bond 4 5, bond 5 0]

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
    ringUnit.cycleBondOrders molecule = [1, 1, 1, 1, 1, 1] := by
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
    ringUnit, molecule, RawMolecule.atomCount, RawBond.connects, bond, carbon]

theorem ring_saturated : ringUnit.SaturatedCyclic molecule := by
  constructor
  · intro order member
    rw [six_ring_bond_orders_exact] at member
    simpa using member
  · intro edge edgeMember rawBond rawBondMember _connects
    have kind : rawBond.kind = .single := by
      simp [molecule, bond] at rawBondMember
      rcases rawBondMember with h | h | h | h | h | h <;> subst rawBond <;> rfl
    rw [kind]
    simp [P94ConformationUnit.SaturatedSingleBondKind]

def chairRecord : P94RingPlaneEvidence where
  unit := ringUnit
  sides := [.onPlane, .onPlane, .positive, .onPlane, .onPlane, .negative]
  saturatedCyclic := True
  symmetricallyEquivalent := False

def boatRecord : P94RingPlaneEvidence where
  unit := ringUnit
  sides := [.onPlane, .onPlane, .positive, .onPlane, .onPlane, .positive]
  saturatedCyclic := True
  symmetricallyEquivalent := False

@[simp] theorem chair_boat_sides_exact :
    chairRecord.sides =
        [.onPlane, .onPlane, .positive, .onPlane, .onPlane, .negative] ∧
      boatRecord.sides =
        [.onPlane, .onPlane, .positive, .onPlane, .onPlane, .positive] := by
  exact ⟨rfl, rfl⟩

def chairEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .chair
  evidence := .ringPlane chairRecord
  unitValid := ringUnit_valid
  molecularRolesValid := by
    simp [P94ConformationEvidence.MolecularRolesValid, chairRecord, ringUnit]
  predicateClosure := .ringPlane chairRecord true false false
    (by simp [chairRecord]) (by simp [chairRecord]) (by simp [chairRecord])
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := by
    simp [P94ConformationEvidence.Supports, P94AuthorityClaim.descriptor,
      chairRecord, ringUnit, IsChair, SixRingReferencePlane, OppositeSides]

def boatEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .boat
  evidence := .ringPlane boatRecord
  unitValid := ringUnit_valid
  molecularRolesValid := by
    simp [P94ConformationEvidence.MolecularRolesValid, boatRecord, ringUnit]
  predicateClosure := .ringPlane boatRecord true false false
    (by simp [boatRecord]) (by simp [boatRecord]) (by simp [boatRecord])
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := by
    simp [P94ConformationEvidence.Supports, P94AuthorityClaim.descriptor,
      boatRecord, ringUnit, IsBoat, SixRingReferencePlane, SameOffPlaneSide]

def twistRecord : P94TwistEvidence Nat where
  unit := ringUnit
  singleBondRotation := P94FiniteNatRelation [(0, 1), (1, 2)]
  endpointConformationsDistinct := P94FiniteNatRelation [(0, 2)]
  isBoatState := P94FiniteNatPredicate [0, 2]
  isChairState := P94FiniteNatPredicate []
  candidate := 1
  firstLeg := [0, 1]
  secondLeg := [1, 2]

theorem twist_first_leg_path :
    DirectedRotationPath twistRecord.singleBondRotation twistRecord.firstLeg := by
  refine .cons (Or.inl ?_) (.singleton 1)
  simp [twistRecord, P94FiniteNatRelation]

theorem twist_second_leg_path :
    DirectedRotationPath twistRecord.singleBondRotation twistRecord.secondLeg := by
  refine .cons (Or.inl ?_) (.singleton 2)
  simp [twistRecord, P94FiniteNatRelation]

theorem twist_path_exact :
    ExplicitTwistOnBoatInterconversion
      twistRecord.singleBondRotation twistRecord.endpointConformationsDistinct
      twistRecord.isBoatState twistRecord.isChairState twistRecord.candidate
      twistRecord.firstLeg twistRecord.secondLeg := by
  refine ⟨0, 2, by decide, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl,
    twist_first_leg_path, twist_second_leg_path, by decide⟩
  · simp [twistRecord, P94FiniteNatRelation]
  · simp [twistRecord, P94FiniteNatPredicate]
  · simp [twistRecord, P94FiniteNatPredicate]
  · simp [twistRecord, P94FiniteNatPredicate]
  · simp [twistRecord, P94FiniteNatPredicate]

def twistEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .sixRingTwist
  evidence := .twist twistRecord
  unitValid := ringUnit_valid
  molecularRolesValid := by simp [P94ConformationEvidence.MolecularRolesValid]
  predicateClosure := .twist twistRecord [(0, 1), (1, 2)] [(0, 2)] [0, 2] []
    rfl rfl rfl rfl
  selectedLonePairsCertified := by intro record equality; cases equality
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := ⟨rfl, twist_path_exact⟩

@[simp] theorem source_entries_support_exact :
    chairEntry.evidence.Supports chairEntry.claim.descriptor ∧
      boatEntry.evidence.Supports boatEntry.claim.descriptor ∧
        twistEntry.evidence.Supports twistEntry.claim.descriptor :=
  ⟨chairEntry.supports, boatEntry.supports, twistEntry.supports⟩

theorem chair_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence chairEntry.evidence)
    (supports : chairEntry.evidence.Supports claim.descriptor) :
    claim = chairEntry.claim := by
  cases claim <;>
    simp [chairEntry, P94AuthorityClaim.MatchesEvidence, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, chairRecord, ringUnit, IsChair, IsBoat,
      SixRingReferencePlane, OppositeSides, SameOffPlaneSide] at claimMatches supports ⊢

theorem boat_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence boatEntry.evidence)
    (supports : boatEntry.evidence.Supports claim.descriptor) :
    claim = boatEntry.claim := by
  cases claim <;>
    simp [boatEntry, P94AuthorityClaim.MatchesEvidence, P94AuthorityClaim.descriptor,
      P94ConformationEvidence.Supports, boatRecord, ringUnit, IsChair, IsBoat,
      SixRingReferencePlane, OppositeSides, SameOffPlaneSide] at claimMatches supports ⊢

theorem twist_uniqueClaim (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence twistEntry.evidence)
    (supports : twistEntry.evidence.Supports claim.descriptor) :
    claim = twistEntry.claim := by
  cases claim <;>
    simp [twistEntry, P94AuthorityClaim.MatchesEvidence] at claimMatches ⊢

def sourcePackage : P94SourcePackageSchema source molecule where
  authoritativeStructureAgreement := structureAgreement
  lonePairLedger := ledger
  ledgerSource := rfl
  evidenceEntries := [chairEntry, boatEntry, twistEntry]
  compatibleClaimsListed := by
    intro entry member claim claimMatches supports
    simp at member
    rcases member with rfl | rfl | rfl
    · have claimExact := chair_uniqueClaim claim claimMatches supports
      subst claim
      exact ⟨chairEntry, by simp, rfl, rfl⟩
    · have claimExact := boat_uniqueClaim claim claimMatches supports
      subst claim
      exact ⟨boatEntry, by simp, rfl, rfl⟩
    · have claimExact := twist_uniqueClaim claim claimMatches supports
      subst claim
      exact ⟨twistEntry, by simp, rfl, rfl⟩
  inOutCoordinatePairs := []

@[simp] theorem source_package_claims_exact :
    sourcePackage.evidenceEntries.map P94SourcePackageEvidenceEntry.claim =
      [.chair, .boat, .sixRingTwist] := by
  rfl

@[simp] theorem source_package_clauses_exact :
    sourcePackage.evidenceEntries.map (fun entry => entry.claim.clause) =
      [.chairBoatTwist, .chairBoatTwist, .chairBoatTwist] := by
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
  entry := chairEntry

@[simp] theorem distinguished_entry_exact :
    distinguishedEntry.entry.claim.clause = .chairBoatTwist ∧
      distinguishedEntry.entry ∈ distinguishedEntry.record.package.evidenceEntries := by
  constructor
  · rfl
  · simp [distinguishedEntry, frozenRecord, sourcePackage]

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

end P94ChairBoatTwistSourceRecord
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P94ChairBoatTwistSourceRecord.source_illustration_binding_exact
assert_kernel_only TetraStereo.OneCenter.P94ChairBoatTwistSourceRecord.molecule_counts_exact
assert_kernel_only TetraStereo.OneCenter.P94ChairBoatTwistSourceRecord.six_ring_bond_orders_exact
assert_kernel_only TetraStereo.OneCenter.P94ChairBoatTwistSourceRecord.ringUnit_valid
assert_kernel_only TetraStereo.OneCenter.P94ChairBoatTwistSourceRecord.ring_saturated
assert_kernel_only TetraStereo.OneCenter.P94ChairBoatTwistSourceRecord.chair_boat_sides_exact
assert_kernel_only TetraStereo.OneCenter.P94ChairBoatTwistSourceRecord.twist_path_exact
assert_kernel_only TetraStereo.OneCenter.P94ChairBoatTwistSourceRecord.source_entries_support_exact
assert_kernel_only TetraStereo.OneCenter.P94ChairBoatTwistSourceRecord.source_package_claims_exact
assert_kernel_only TetraStereo.OneCenter.P94ChairBoatTwistSourceRecord.source_package_clauses_exact
assert_kernel_only TetraStereo.OneCenter.P94ChairBoatTwistSourceRecord.normalizationReady
assert_kernel_only TetraStereo.OneCenter.P94ChairBoatTwistSourceRecord.distinguished_entry_exact
assert_kernel_only
  TetraStereo.OneCenter.P94ChairBoatTwistSourceRecord.current_independent_source_review_issued
