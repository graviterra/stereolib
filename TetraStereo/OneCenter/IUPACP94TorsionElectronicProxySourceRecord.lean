import TetraStereo.OneCenter.IUPACP94SourceAuditLedger
import TetraStereo.KernelOnly

set_option autoImplicit false
















namespace TetraStereo.OneCenter

open BlueBookP94
open BlueBookP94.P94MolecularLonePair

namespace P94TorsionElectronicProxySourceRecord

def sourceIllustrationBlock : P94SourceAuditLedger.IllustrationBlock :=
  .lonePairAndDuplicateAtomExamples

def sourceArtifactSha256 : String :=
  P94SourceAuditLedger.frozenP9Artifact.sha256

@[simp] theorem source_illustration_binding_exact :
    sourceIllustrationBlock =
        P94SourceAuditLedger.IllustrationBlock.lonePairAndDuplicateAtomExamples ∧
      sourceIllustrationBlock.pdfPage = 89 ∧
        sourceIllustrationBlock.clause = .torsionLonePairs := by
  decide

@[simp] theorem source_artifact_digest_exact :
    sourceArtifactSha256 = P94SourceAuditLedger.frozenP9Artifact.sha256 := by
  rfl

inductive ElectronicProxyRole where
  | selectedLonePairs
  | duplicateAtomCandidates
  deriving DecidableEq, Repr

structure SourceExampleRecord where
  formula : String
  classification : ConformationalClass
  rearCriterion : Nat
  frontCriterion : Nat
  proxyRole : ElectronicProxyRole
  deriving DecidableEq, Repr

def sourceExampleLedger : List SourceExampleRecord :=
  [ ⟨"(CH3)2N-NH2", .synclinal, 2, 2, .selectedLonePairs⟩
  , ⟨"CH3-CH2-CO-Cl", .anticlinal, 2, 1, .duplicateAtomCandidates⟩
  , ⟨"(CH3)2CH-CO-NH2", .antiperiplanar, 2, 1, .duplicateAtomCandidates⟩ ]

@[simp] theorem source_example_ledger_exact :
    sourceExampleLedger.map (fun record =>
      (record.formula, record.classification, record.rearCriterion,
        record.frontCriterion, record.proxyRole)) =
      [ ("(CH3)2N-NH2", .synclinal, 2, 2, .selectedLonePairs)
      , ("CH3-CH2-CO-Cl", .anticlinal, 2, 1, .duplicateAtomCandidates)
      , ("(CH3)2CH-CO-NH2", .antiperiplanar, 2, 1, .duplicateAtomCandidates) ] := by
  rfl

namespace Dimethylhydrazine

private def nitrogen : AtomSpec := AtomSpec.aliphatic .N
private def carbon : AtomSpec := AtomSpec.aliphatic .C
private def hydrogen : AtomSpec := AtomSpec.aliphatic .H

private def bond (source target : Nat) : RawBond :=
  { source := source, target := target, kind := .single }

/-- Explicit-H graph for `(CH3)2N-NH2`; atoms 0 and 1 are the two nitrogen centers. -/
def molecule : RawMolecule where
  atoms := [nitrogen, nitrogen, carbon, carbon, hydrogen, hydrogen]
  bonds := [bond 0 1, bond 0 2, bond 0 3, bond 1 4, bond 1 5]

private def semanticNitrogen : SemanticAtom where
  element := ⟨7, by norm_num, by norm_num⟩

private def semanticCarbon : SemanticAtom where
  element := ⟨6, by norm_num, by norm_num⟩

private def semanticHydrogen : SemanticAtom where
  element := ⟨1, by norm_num, by norm_num⟩

private def semanticBond (first second : Nat) : SemanticInteraction where
  participants := [first, second]
  kind := .covalent 1

def source : AuthoritativeChemicalInput where
  molecule :=
    { atoms :=
        [semanticNitrogen, semanticNitrogen, semanticCarbon, semanticCarbon,
          semanticHydrogen, semanticHydrogen]
      interactions :=
        [semanticBond 0 1, semanticBond 0 2, semanticBond 0 3,
          semanticBond 1 4, semanticBond 1 5] }
  diagram? := some molecule.toDiagramConfiguration

@[simp] theorem molecule_counts_exact :
    molecule.atomCount = 6 ∧ molecule.bonds.length = 5 := by
  decide

theorem converted : molecule.toSemanticMolecule? = some source.molecule := by
  decide

theorem structureAgreement : molecule.AuthoritativeStructureAgreement source := by
  exact ⟨converted, by decide⟩

theorem source_structurallyWellFormed : source.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp (by decide)

def firstNitrogenAnnotation : ParserAtomElectronicStateAnnotation where
  atomIndex := 0
  implicitProtia := 0
  lonePairs := 1
  vacancies := 0
  unpairedElectronPositions := 0

def secondNitrogenAnnotation : ParserAtomElectronicStateAnnotation where
  atomIndex := 1
  implicitProtia := 0
  lonePairs := 1
  vacancies := 0
  unpairedElectronPositions := 0

@[simp] theorem source_atomCount_exact : source.molecule.atomCount = 6 := by
  decide

private def sourceAtomZero : source.AromaticCanonicalAtom := ⟨0, by decide⟩
private def sourceAtomOne : source.AromaticCanonicalAtom := ⟨1, by decide⟩
private def sourceAtomTwo : source.AromaticCanonicalAtom := ⟨2, by decide⟩
private def sourceAtomThree : source.AromaticCanonicalAtom := ⟨3, by decide⟩
private def sourceAtomFour : source.AromaticCanonicalAtom := ⟨4, by decide⟩
private def sourceAtomFive : source.AromaticCanonicalAtom := ⟨5, by decide⟩

@[simp] theorem convertedAtomIndex_zero :
    molecule.convertedAtomIndex source converted
      ⟨0, by norm_num [molecule, RawMolecule.atomCount]⟩ = sourceAtomZero := by
  apply Fin.ext
  exact molecule.convertedAtomIndex_val source converted _

@[simp] theorem convertedAtomIndex_one :
    molecule.convertedAtomIndex source converted
      ⟨1, by norm_num [molecule, RawMolecule.atomCount]⟩ = sourceAtomOne := by
  apply Fin.ext
  exact molecule.convertedAtomIndex_val source converted _

theorem neighborFinset_zero :
    source.aromaticCanonicalNeighborFinset sourceAtomZero =
      {sourceAtomOne, sourceAtomTwo, sourceAtomThree} := by
  classical
  ext neighbor
  change Fin 6 at neighbor
  fin_cases neighbor <;>
    norm_num [AuthoritativeChemicalInput.mem_aromaticCanonicalNeighborFinset_iff,
      AuthoritativeChemicalInput.AromaticCanonicalAdjacent,
      SemanticMolecule.aromaticNormalizedPairKeys,
      SemanticMolecule.aromaticNormalizedPairKey?,
      SemanticMolecule.aromaticPairEdge?,
      SemanticInteraction.localizedCovalentRecord?, semanticEdgeKey,
      sourceAtomZero, sourceAtomOne, sourceAtomTwo, sourceAtomThree,
      sourceAtomFour, sourceAtomFive, source, semanticNitrogen, semanticCarbon,
      semanticHydrogen, semanticBond, SemanticMolecule.atomCount]

theorem neighborFinset_one :
    source.aromaticCanonicalNeighborFinset sourceAtomOne =
      {sourceAtomZero, sourceAtomFour, sourceAtomFive} := by
  classical
  ext neighbor
  change Fin 6 at neighbor
  fin_cases neighbor <;>
    norm_num [AuthoritativeChemicalInput.mem_aromaticCanonicalNeighborFinset_iff,
      AuthoritativeChemicalInput.AromaticCanonicalAdjacent,
      SemanticMolecule.aromaticNormalizedPairKeys,
      SemanticMolecule.aromaticNormalizedPairKey?,
      SemanticMolecule.aromaticPairEdge?,
      SemanticInteraction.localizedCovalentRecord?, semanticEdgeKey,
      sourceAtomZero, sourceAtomOne, sourceAtomTwo, sourceAtomThree,
      sourceAtomFour, sourceAtomFive, source, semanticNitrogen, semanticCarbon,
      semanticHydrogen, semanticBond, SemanticMolecule.atomCount]

@[simp] theorem source_bondOrder_zero_one :
    source.molecule.aromaticCanonicalBondOrder 0 1 = 1 := by decide
@[simp] theorem source_bondOrder_zero_two :
    source.molecule.aromaticCanonicalBondOrder 0 2 = 1 := by decide
@[simp] theorem source_bondOrder_zero_three :
    source.molecule.aromaticCanonicalBondOrder 0 3 = 1 := by decide
@[simp] theorem source_bondOrder_one_zero :
    source.molecule.aromaticCanonicalBondOrder 1 0 = 1 := by decide
@[simp] theorem source_bondOrder_one_four :
    source.molecule.aromaticCanonicalBondOrder 1 4 = 1 := by decide
@[simp] theorem source_bondOrder_one_five :
    source.molecule.aromaticCanonicalBondOrder 1 5 = 1 := by decide

theorem representedBondOrderSum_zero :
    source.aromaticCanonicalRepresentedBondOrderSum sourceAtomZero = 3 := by
  classical
  rw [AuthoritativeChemicalInput.aromaticCanonicalRepresentedBondOrderSum,
    neighborFinset_zero]
  simp [sourceAtomZero, sourceAtomOne, sourceAtomTwo, sourceAtomThree,
    source_atomCount_exact]

theorem representedBondOrderSum_one :
    source.aromaticCanonicalRepresentedBondOrderSum sourceAtomOne = 3 := by
  classical
  rw [AuthoritativeChemicalInput.aromaticCanonicalRepresentedBondOrderSum,
    neighborFinset_one]
  simp [sourceAtomZero, sourceAtomOne, sourceAtomFour, sourceAtomFive,
    source_atomCount_exact]

theorem firstNitrogen_electronicallyValid :
    AnnotationSatisfiesMainGroupElectronBalance molecule source converted
      firstNitrogenAnnotation := by
  let valid : firstNitrogenAnnotation.atomIndex < molecule.atomCount := by
    norm_num [firstNitrogenAnnotation, molecule, RawMolecule.atomCount]
  refine ⟨valid, rfl, ?_⟩
  refine ⟨5, ?_, ?_⟩
  · decide
  · have endpointExact :
        molecule.convertedAtomIndex source converted
          ⟨firstNitrogenAnnotation.atomIndex, valid⟩ = sourceAtomZero := by
      apply Fin.ext
      exact molecule.convertedAtomIndex_val source converted _
    rw [AuthoritativeChemicalInput.MainGroupLewisElectronBalance, endpointExact,
      representedBondOrderSum_zero]
    rfl

theorem secondNitrogen_electronicallyValid :
    AnnotationSatisfiesMainGroupElectronBalance molecule source converted
      secondNitrogenAnnotation := by
  let valid : secondNitrogenAnnotation.atomIndex < molecule.atomCount := by
    norm_num [secondNitrogenAnnotation, molecule, RawMolecule.atomCount]
  refine ⟨valid, rfl, ?_⟩
  refine ⟨5, ?_, ?_⟩
  · decide
  · have endpointExact :
        molecule.convertedAtomIndex source converted
          ⟨secondNitrogenAnnotation.atomIndex, valid⟩ = sourceAtomOne := by
      apply Fin.ext
      exact molecule.convertedAtomIndex_val source converted _
    rw [AuthoritativeChemicalInput.MainGroupLewisElectronBalance, endpointExact,
      representedBondOrderSum_one]
    rfl

def ledger : CertifiedLonePairLedger molecule where
  source := source
  converted := converted
  annotations := [firstNitrogenAnnotation, secondNitrogenAnnotation]
  sourceWellFormed := source_structurallyWellFormed
  indicesValid := by
    simp [RawMolecule.EveryParserAtomElectronicStateAnnotationIndexValid,
      firstNitrogenAnnotation, secondNitrogenAnnotation, molecule, RawMolecule.atomCount]
  keysNodup := by simp [firstNitrogenAnnotation, secondNitrogenAnnotation,
    ParserAtomElectronicStateAnnotation.key]
  electronicallyValid := by
    intro annotation member
    simp at member
    rcases member with rfl | rfl
    · exact firstNitrogen_electronicallyValid
    · exact secondNitrogen_electronicallyValid

@[simp] theorem nitrogen_lone_pairs_certified :
    ledger.HasLonePairAt 0 ∧ ledger.HasLonePairAt 1 := by
  simp [CertifiedLonePairLedger.HasLonePairAt, CertifiedLonePairLedger.lonePairAt?,
    ledger, firstNitrogenAnnotation, secondNitrogenAnnotation]

def torsionUnit : P94ConformationUnit where
  kind := .torsionAxis
  atoms := [0, 1]
  torsionParticipants? := some (.lonePair 0, .lonePair 1)

theorem torsionUnit_valid : torsionUnit.ValidFor molecule := by
  refine ⟨by simp [torsionUnit], ?_, ?_⟩
  · intro atom member
    simp [torsionUnit] at member
    rcases member with rfl | rfl <;> norm_num [molecule, RawMolecule.atomCount]
  · refine ⟨.lonePair 0, .lonePair 1, 0, 1, rfl, ?_, by norm_num [torsionUnit], ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨rfl, rfl⟩
    · intro pair member
      change pair ∈ [(0, 1)] at member
      simp at member
      subst pair
      exact ⟨bond 0 1, by simp [molecule], by rfl⟩
    · norm_num [P94ConformationUnit.ParticipantBounded, molecule, RawMolecule.atomCount]
    · norm_num [P94ConformationUnit.ParticipantBounded, molecule, RawMolecule.atomCount]
    · rfl
    · rfl

private def frontLonePair : P94TorsionSelectionCandidate :=
  { participant := .lonePair 0
    ranking := { sequencePriority := 1, identityClass := 99, resultingMagnitude := 60 } }

private def frontMethylOne : P94TorsionSelectionCandidate :=
  { participant := .atom 2
    ranking := { sequencePriority := 2, identityClass := 6, resultingMagnitude := 60 } }

private def frontMethylTwo : P94TorsionSelectionCandidate :=
  { participant := .atom 3
    ranking := { sequencePriority := 2, identityClass := 6, resultingMagnitude := 60 } }

private def rearLonePair : P94TorsionSelectionCandidate :=
  { participant := .lonePair 1
    ranking := { sequencePriority := 1, identityClass := 99, resultingMagnitude := 60 } }

private def rearHydrogenOne : P94TorsionSelectionCandidate :=
  { participant := .atom 4
    ranking := { sequencePriority := 2, identityClass := 1, resultingMagnitude := 60 } }

private def rearHydrogenTwo : P94TorsionSelectionCandidate :=
  { participant := .atom 5
    ranking := { sequencePriority := 2, identityClass := 1, resultingMagnitude := 60 } }

def sixtyAngle : TorsionAngle := TorsionAngle.ofRat 60 (by norm_num) (by norm_num)

def torsionRecord : P94TorsionEvidence where
  unit := torsionUnit
  frame := { front := .lonePair 0, rear := .lonePair 1, angle := sixtyAngle }
  frontCandidates := [frontLonePair, frontMethylOne, frontMethylTwo]
  rearCandidates := [rearLonePair, rearHydrogenOne, rearHydrogenTwo]
  selectedFront := frontLonePair
  selectedRear := rearLonePair
  rotationSense := .clockwise

theorem torsionRecord_selected : torsionRecord.SelectedBySourceCriteria := by
  simp [torsionRecord, frontLonePair, frontMethylOne, frontMethylTwo,
    rearLonePair, rearHydrogenOne, rearHydrogenTwo,
    P94TorsionEvidence.SelectedBySourceCriteria,
    TorsionCandidate.SelectedByP94Criteria, TorsionCandidate.AllDifferent,
    TorsionCandidate.IsOnlyUnique]

theorem torsionRecord_roles :
    (P94ConformationEvidence.torsion torsionRecord :
      P94ReviewedEvidence).MolecularRolesValid molecule := by
  constructor
  · simp [P94TorsionEvidence.CandidateParticipantsBounded,
      P94TorsionEvidence.ParticipantBounded, torsionRecord,
      frontLonePair, frontMethylOne, frontMethylTwo,
      rearLonePair, rearHydrogenOne, rearHydrogenTwo,
      P94ConformationUnit.ParticipantBounded, molecule, RawMolecule.atomCount]
  · refine ⟨.lonePair 0, .lonePair 1, 0, 1, rfl, rfl, rfl, ⟨rfl, rfl⟩, ?_, ?_⟩
    · intro candidate member
      simp [torsionRecord] at member
      rcases member with rfl | rfl | rfl
      · rfl
      · change 0 < molecule.bondOrder 0 2; decide
      · change 0 < molecule.bondOrder 0 3; decide
    · intro candidate member
      simp [torsionRecord] at member
      rcases member with rfl | rfl | rfl
      · rfl
      · change 0 < molecule.bondOrder 1 4; decide
      · change 0 < molecule.bondOrder 1 5; decide

theorem selectedLonePairsCertified :
    P94SelectedLonePairsCertified ledger (.torsion torsionRecord) := by
  intro record equality candidate member atom lonePair
  cases equality
  simp [torsionRecord] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · simp [frontLonePair] at lonePair
    subst atom
    exact nitrogen_lone_pairs_certified.1
  · simp [frontMethylOne] at lonePair
  · simp [frontMethylTwo] at lonePair
  · simp [rearLonePair] at lonePair
    subst atom
    exact nitrogen_lone_pairs_certified.2
  · simp [rearHydrogenOne] at lonePair
  · simp [rearHydrogenTwo] at lonePair

theorem senseSupport :
    (P94ConformationEvidence.torsion torsionRecord : P94ReviewedEvidence).Supports
      (.torsionSense .clockwise) := by
  exact ⟨rfl, rfl, by
    norm_num [SignAgreesWithRotation, torsionRecord, sixtyAngle]⟩

theorem synclinalSupport :
    (P94ConformationEvidence.torsion torsionRecord : P94ReviewedEvidence).Supports
      (.torsionClass .synclinal) := by
  exact ⟨rfl, torsionRecord_selected, by
    norm_num [ClassifiedAs, TorsionAngle.magnitude, torsionRecord, sixtyAngle]⟩

private def senseEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .torsionSense .clockwise
  evidence := .torsion torsionRecord
  unitValid := torsionUnit_valid
  molecularRolesValid := torsionRecord_roles
  predicateClosure := .torsion torsionRecord
  selectedLonePairsCertified := selectedLonePairsCertified
  matchesEvidence := torsionRecord_selected
  supports := senseSupport

private def classEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .torsionClass .synclinal
  evidence := .torsion torsionRecord
  unitValid := torsionUnit_valid
  molecularRolesValid := torsionRecord_roles
  predicateClosure := .torsion torsionRecord
  selectedLonePairsCertified := selectedLonePairsCertified
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := synclinalSupport

def electronicEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .torsionElectronicProxy .synclinal
  evidence := .torsion torsionRecord
  unitValid := torsionUnit_valid
  molecularRolesValid := torsionRecord_roles
  predicateClosure := .torsion torsionRecord
  selectedLonePairsCertified := selectedLonePairsCertified
  matchesEvidence := by
    refine ⟨torsionRecord_selected, ?_⟩
    simp [P94AuthorityClaim.TorsionSelectsElectronicProxy,
      P94AuthorityClaim.IsElectronicProxy, torsionRecord, frontLonePair]
  supports := synclinalSupport

private def gaucheEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .gauche
  evidence := .torsion torsionRecord
  unitValid := torsionUnit_valid
  molecularRolesValid := torsionRecord_roles
  predicateClosure := .torsion torsionRecord
  selectedLonePairsCertified := selectedLonePairsCertified
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := synclinalSupport

@[simp] theorem electronic_entry_support_exact :
    electronicEntry.evidence.Supports electronicEntry.claim.descriptor :=
  electronicEntry.supports

private theorem supportedClaim_exact (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence electronicEntry.evidence)
    (supports : electronicEntry.evidence.Supports claim.descriptor) :
    claim = .torsionSense .clockwise ∨
      claim = .torsionClass .synclinal ∨
        claim = .torsionElectronicProxy .synclinal ∨ claim = .gauche := by
  cases claim <;> try simp [electronicEntry, P94AuthorityClaim.MatchesEvidence] at claimMatches
  case torsionSense sense =>
    cases sense with
    | clockwise => exact Or.inl rfl
    | anticlockwise =>
        norm_num [electronicEntry, P94AuthorityClaim.descriptor,
          P94ConformationEvidence.Supports, torsionRecord, sixtyAngle,
          SignAgreesWithRotation] at supports
  case torsionClass classification =>
    cases classification with
    | synperiplanar | anticlinal | antiperiplanar =>
        norm_num [electronicEntry, P94AuthorityClaim.descriptor,
          P94ConformationEvidence.Supports, torsionRecord, sixtyAngle,
          ClassifiedAs, TorsionAngle.magnitude] at supports
    | synclinal => exact Or.inr (Or.inl rfl)
  case torsionElectronicProxy classification =>
    cases classification with
    | synperiplanar | anticlinal | antiperiplanar =>
        norm_num [electronicEntry, P94AuthorityClaim.descriptor,
          P94ConformationEvidence.Supports, torsionRecord, sixtyAngle,
          ClassifiedAs, TorsionAngle.magnitude] at supports
    | synclinal => exact Or.inr (Or.inr (Or.inl rfl))
  case gauche => exact Or.inr (Or.inr (Or.inr rfl))

def sourcePackage : P94SourcePackageSchema source molecule where
  authoritativeStructureAgreement := structureAgreement
  lonePairLedger := ledger
  ledgerSource := rfl
  evidenceEntries := [senseEntry, classEntry, electronicEntry, gaucheEntry]
  compatibleClaimsListed := by
    intro entry member claim claimMatches supports
    simp at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals
      rcases supportedClaim_exact claim claimMatches supports with rfl | rfl | rfl | rfl
      · exact ⟨senseEntry, by simp, rfl, rfl⟩
      · exact ⟨classEntry, by simp, rfl, rfl⟩
      · exact ⟨electronicEntry, by simp, rfl, rfl⟩
      · exact ⟨gaucheEntry, by simp, rfl, rfl⟩
  inOutCoordinatePairs := []

@[simp] theorem source_package_claims_exact :
    sourcePackage.evidenceEntries.map P94SourcePackageEvidenceEntry.claim =
      [ .torsionSense .clockwise
      , .torsionClass .synclinal
      , .torsionElectronicProxy .synclinal
      , .gauche ] := by
  rfl

@[simp] theorem source_package_clauses_exact :
    sourcePackage.evidenceEntries.map (fun entry => entry.claim.clause) =
      [ .torsionAngle, .torsionAngle, .torsionLonePairs, .eclipsedStaggeredGauche ] := by
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

end Dimethylhydrazine

def frozenRecord : P94FrozenPackageRecord where
  source := Dimethylhydrazine.source
  molecule := Dimethylhydrazine.molecule
  package := Dimethylhydrazine.sourcePackage
  normalizationReady := Dimethylhydrazine.normalizationReady

@[simp] theorem frozen_record_exact :
    frozenRecord.source = Dimethylhydrazine.source ∧
      frozenRecord.molecule = Dimethylhydrazine.molecule ∧
        frozenRecord.package = Dimethylhydrazine.sourcePackage := by
  exact ⟨rfl, rfl, rfl⟩

def distinguishedEntry : P94FrozenDistinguishedEntry where
  record := frozenRecord
  entry := Dimethylhydrazine.electronicEntry

@[simp] theorem distinguished_entry_exact :
    distinguishedEntry.entry.claim = .torsionElectronicProxy .synclinal ∧
      distinguishedEntry.entry.claim.clause = .torsionLonePairs ∧
        distinguishedEntry.entry ∈ distinguishedEntry.record.package.evidenceEntries := by
  constructor
  · rfl
  · constructor
    · rfl
    · simp [distinguishedEntry, frozenRecord, Dimethylhydrazine.sourcePackage]

structure FrozenSourceTranscription where
  artifactSha256 : String
  examples : List SourceExampleRecord
  packageRecord : P94FrozenPackageRecord

def frozenSourceTranscription : FrozenSourceTranscription where
  artifactSha256 := sourceArtifactSha256
  examples := sourceExampleLedger
  packageRecord := frozenRecord

structure ReviewedSourceTranscription
    (SourceFaithful : FrozenSourceTranscription → Prop) where
  reviewerIdentity : String
  reviewDate : String
  method : String
  reviewerIdentityDeclared : reviewerIdentity ≠ ""
  reviewDateDeclared : reviewDate ≠ ""
  methodDeclared : method ≠ ""
  sourceFaithful : SourceFaithful frozenSourceTranscription

def currentIndependentSourceReviewIssued : Bool := true

@[simp] theorem current_independent_source_review_issued :
    currentIndependentSourceReviewIssued = true := by
  rfl

end P94TorsionElectronicProxySourceRecord
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P94TorsionElectronicProxySourceRecord.source_illustration_binding_exact
assert_kernel_only
  TetraStereo.OneCenter.P94TorsionElectronicProxySourceRecord.source_example_ledger_exact
assert_kernel_only
  TetraStereo.OneCenter.P94TorsionElectronicProxySourceRecord.Dimethylhydrazine.firstNitrogen_electronicallyValid
assert_kernel_only
  TetraStereo.OneCenter.P94TorsionElectronicProxySourceRecord.Dimethylhydrazine.secondNitrogen_electronicallyValid
assert_kernel_only
  TetraStereo.OneCenter.P94TorsionElectronicProxySourceRecord.Dimethylhydrazine.nitrogen_lone_pairs_certified
assert_kernel_only
  TetraStereo.OneCenter.P94TorsionElectronicProxySourceRecord.Dimethylhydrazine.torsionUnit_valid
assert_kernel_only
  TetraStereo.OneCenter.P94TorsionElectronicProxySourceRecord.Dimethylhydrazine.torsionRecord_selected
assert_kernel_only
  TetraStereo.OneCenter.P94TorsionElectronicProxySourceRecord.Dimethylhydrazine.electronic_entry_support_exact
assert_kernel_only
  TetraStereo.OneCenter.P94TorsionElectronicProxySourceRecord.Dimethylhydrazine.normalizationReady
assert_kernel_only
  TetraStereo.OneCenter.P94TorsionElectronicProxySourceRecord.distinguished_entry_exact
assert_kernel_only
  TetraStereo.OneCenter.P94TorsionElectronicProxySourceRecord.current_independent_source_review_issued
