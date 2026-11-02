import TetraStereo.OneCenter.IUPACP94SourceAuditLedger
import TetraStereo.KernelOnly

set_option autoImplicit false















namespace TetraStereo.OneCenter

open BlueBookP94
open BlueBookP94.P94MolecularLonePair

namespace P94TorsionAngleSourceRecord

def sourceIllustrationBlocks : List P94SourceAuditLedger.IllustrationBlock :=
  [ .torsionClassAngleDiagram
  , .torsionHalogenExamples
  , .torsionSelectionCriteriaExamples ]

def sourceArtifactSha256 : String :=
  P94SourceAuditLedger.frozenP9Artifact.sha256

@[simp] theorem source_illustration_bindings_exact :
    sourceIllustrationBlocks.map P94SourceAuditLedger.IllustrationBlock.pdfPage =
        [88, 88, 88] ∧
      sourceIllustrationBlocks.map P94SourceAuditLedger.IllustrationBlock.clause =
        [.torsionAngle, .torsionAngle, .torsionAngle] := by
  decide

@[simp] theorem source_artifact_digest_exact :
    sourceArtifactSha256 = P94SourceAuditLedger.frozenP9Artifact.sha256 := by
  rfl

structure TorsionClassBoundary where
  classification : ConformationalClass
  magnitudeLower : Nat
  magnitudeUpper : Nat
  signedCenters : List Int
  deriving DecidableEq, Repr

def classBoundaries : List TorsionClassBoundary :=
  [ ⟨.synperiplanar, 0, 30, [0]⟩
  , ⟨.synclinal, 30, 90, [-60, 60]⟩
  , ⟨.anticlinal, 90, 150, [-120, 120]⟩
  , ⟨.antiperiplanar, 150, 180, [-180, 180]⟩ ]

def boundaryMagnitudes : List Nat := [30, 90, 150]

@[simp] theorem class_boundaries_exact :
    classBoundaries.map (fun boundary =>
      (boundary.classification, boundary.magnitudeLower, boundary.magnitudeUpper,
        boundary.signedCenters)) =
      [ (.synperiplanar, 0, 30, [0])
      , (.synclinal, 30, 90, [-60, 60])
      , (.anticlinal, 90, 150, [-120, 120])
      , (.antiperiplanar, 150, 180, [-180, 180]) ] := by
  rfl

@[simp] theorem inclusive_class_boundaries_exact :
    ClassifiedAs (TorsionAngle.ofRat 30 (by norm_num) (by norm_num)) .synperiplanar ∧
      ClassifiedAs (TorsionAngle.ofRat 30 (by norm_num) (by norm_num)) .synclinal ∧
        ClassifiedAs (TorsionAngle.ofRat 90 (by norm_num) (by norm_num)) .synclinal ∧
          ClassifiedAs (TorsionAngle.ofRat 90 (by norm_num) (by norm_num)) .anticlinal ∧
            ClassifiedAs (TorsionAngle.ofRat 150 (by norm_num) (by norm_num)) .anticlinal ∧
              ClassifiedAs (TorsionAngle.ofRat 150 (by norm_num) (by norm_num))
                .antiperiplanar := by
  norm_num [ClassifiedAs, TorsionAngle.magnitude]

def halogenExampleClasses : List ConformationalClass :=
  [.antiperiplanar, .anticlinal, .synclinal, .synperiplanar]

inductive SelectionCriterion where
  | allDifferentSequenceRule
  | oneUnique
  | allIdenticalSmallestAngle
  deriving DecidableEq, Repr

namespace SelectionCriterion

def number : SelectionCriterion → Nat
  | .allDifferentSequenceRule => 1
  | .oneUnique => 2
  | .allIdenticalSmallestAngle => 3

end SelectionCriterion

def selectionCriteria : List SelectionCriterion :=
  [.allDifferentSequenceRule, .oneUnique, .allIdenticalSmallestAngle]

structure SelectionExampleRecord where
  classification : ConformationalClass
  rearCriterion : SelectionCriterion
  frontCriterion : SelectionCriterion
  deriving DecidableEq, Repr

def selectionExampleLedger : List SelectionExampleRecord :=
  [ ⟨.synclinal, .oneUnique, .oneUnique⟩
  , ⟨.anticlinal, .oneUnique, .oneUnique⟩
  , ⟨.synclinal, .allIdenticalSmallestAngle, .oneUnique⟩
  , ⟨.synperiplanar, .allDifferentSequenceRule, .allDifferentSequenceRule⟩ ]

@[simp] theorem selection_example_ledger_exact :
    selectionExampleLedger.map (fun record =>
      (record.classification, record.rearCriterion.number, record.frontCriterion.number)) =
      [ (.synclinal, 2, 2), (.anticlinal, 2, 2)
      , (.synclinal, 3, 2), (.synperiplanar, 1, 1) ] := by
  rfl

namespace HalogenSpecialization

private def carbon : AtomSpec := AtomSpec.aliphatic .C
private def hydrogen : AtomSpec := AtomSpec.aliphatic .H
private def chlorine : AtomSpec := AtomSpec.aliphatic .Cl

private def bond (source target : Nat) : RawBond :=
  { source := source, target := target, kind := .single }

/-- Explicit-H 1,2-dichloroethane shared by the four first-row Newman examples. -/
def molecule : RawMolecule where
  atoms := [carbon, carbon, chlorine, chlorine, hydrogen, hydrogen, hydrogen, hydrogen]
  bonds :=
    [bond 0 1, bond 0 2, bond 0 4, bond 0 5, bond 1 3, bond 1 6, bond 1 7]

def source : AuthoritativeChemicalInput :=
  match molecule.toSemanticMolecule? with
  | none => { molecule := { atoms := [], interactions := [] } }
  | some semantic =>
      { molecule := semantic
        diagram? := some molecule.toDiagramConfiguration }

@[simp] theorem molecule_counts_exact :
    molecule.atomCount = 8 ∧ molecule.bonds.length = 7 := by
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

def torsionUnit : P94ConformationUnit where
  kind := .torsionAxis
  atoms := [0, 1]
  torsionParticipants? := some (.atom 2, .atom 3)

theorem torsionUnit_valid : torsionUnit.ValidFor molecule := by
  refine ⟨by simp [torsionUnit], ?_, ?_⟩
  · intro atom member
    simp [torsionUnit] at member
    rcases member with rfl | rfl <;> norm_num [molecule, RawMolecule.atomCount]
  · refine ⟨.atom 2, .atom 3, 0, 1, rfl, ?_, by norm_num [torsionUnit], ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨rfl, rfl⟩
    · intro pair member
      change pair ∈ [(0, 1)] at member
      simp at member
      subst pair
      exact ⟨bond 0 1, by simp [molecule], by rfl⟩
    · norm_num [P94ConformationUnit.ParticipantBounded, molecule, RawMolecule.atomCount]
    · norm_num [P94ConformationUnit.ParticipantBounded, molecule, RawMolecule.atomCount]
    · change 0 < molecule.bondOrder 0 2
      decide
    · change 0 < molecule.bondOrder 1 3
      decide

private def frontChlorine : P94TorsionSelectionCandidate :=
  { participant := .atom 2
    ranking := { sequencePriority := 1, identityClass := 17, resultingMagnitude := 0 } }

private def frontHydrogenOne : P94TorsionSelectionCandidate :=
  { participant := .atom 4
    ranking := { sequencePriority := 2, identityClass := 1, resultingMagnitude := 0 } }

private def frontHydrogenTwo : P94TorsionSelectionCandidate :=
  { participant := .atom 5
    ranking := { sequencePriority := 2, identityClass := 1, resultingMagnitude := 0 } }

private def rearChlorine : P94TorsionSelectionCandidate :=
  { participant := .atom 3
    ranking := { sequencePriority := 1, identityClass := 17, resultingMagnitude := 0 } }

private def rearHydrogenOne : P94TorsionSelectionCandidate :=
  { participant := .atom 6
    ranking := { sequencePriority := 2, identityClass := 1, resultingMagnitude := 0 } }

private def rearHydrogenTwo : P94TorsionSelectionCandidate :=
  { participant := .atom 7
    ranking := { sequencePriority := 2, identityClass := 1, resultingMagnitude := 0 } }

def torsionRecord (angle : TorsionAngle) : P94TorsionEvidence where
  unit := torsionUnit
  frame := { front := .atom 2, rear := .atom 3, angle := angle }
  frontCandidates := [frontChlorine, frontHydrogenOne, frontHydrogenTwo]
  rearCandidates := [rearChlorine, rearHydrogenOne, rearHydrogenTwo]
  selectedFront := frontChlorine
  selectedRear := rearChlorine
  rotationSense := .clockwise

def apAngle : TorsionAngle := TorsionAngle.ofRat 180 (by norm_num) (by norm_num)
def acAngle : TorsionAngle := TorsionAngle.ofRat 120 (by norm_num) (by norm_num)
def scAngle : TorsionAngle := TorsionAngle.ofRat 60 (by norm_num) (by norm_num)
def spAngle : TorsionAngle := TorsionAngle.ofRat 0 (by norm_num) (by norm_num)

def apRecord : P94TorsionEvidence := torsionRecord apAngle
def acRecord : P94TorsionEvidence := torsionRecord acAngle
def scRecord : P94TorsionEvidence := torsionRecord scAngle
def spRecord : P94TorsionEvidence := torsionRecord spAngle

theorem torsionRecord_selected (angle : TorsionAngle) :
    (torsionRecord angle).SelectedBySourceCriteria := by
  simp [torsionRecord, frontChlorine, frontHydrogenOne, frontHydrogenTwo,
    rearChlorine, rearHydrogenOne, rearHydrogenTwo,
    P94TorsionEvidence.SelectedBySourceCriteria,
    TorsionCandidate.SelectedByP94Criteria, TorsionCandidate.AllDifferent,
    TorsionCandidate.IsOnlyUnique]

@[simp] theorem records_selected_exact :
    apRecord.SelectedBySourceCriteria ∧ acRecord.SelectedBySourceCriteria ∧
      scRecord.SelectedBySourceCriteria ∧ spRecord.SelectedBySourceCriteria := by
  exact ⟨torsionRecord_selected apAngle, torsionRecord_selected acAngle,
    torsionRecord_selected scAngle, torsionRecord_selected spAngle⟩

theorem torsionRecord_roles (angle : TorsionAngle) :
    (P94ConformationEvidence.torsion (torsionRecord angle) :
      P94ReviewedEvidence).MolecularRolesValid molecule := by
  constructor
  · simp [P94TorsionEvidence.CandidateParticipantsBounded,
      P94TorsionEvidence.ParticipantBounded, torsionRecord,
      frontChlorine, frontHydrogenOne, frontHydrogenTwo,
      rearChlorine, rearHydrogenOne, rearHydrogenTwo,
      P94ConformationUnit.ParticipantBounded, molecule, RawMolecule.atomCount]
  · refine ⟨.atom 2, .atom 3, 0, 1, rfl, rfl, rfl, ⟨rfl, rfl⟩, ?_, ?_⟩
    · intro candidate member
      simp [torsionRecord] at member
      rcases member with rfl | rfl | rfl
      · change 0 < molecule.bondOrder 0 2; decide
      · change 0 < molecule.bondOrder 0 4; decide
      · change 0 < molecule.bondOrder 0 5; decide
    · intro candidate member
      simp [torsionRecord] at member
      rcases member with rfl | rfl | rfl
      · change 0 < molecule.bondOrder 1 3; decide
      · change 0 < molecule.bondOrder 1 6; decide
      · change 0 < molecule.bondOrder 1 7; decide

private theorem selectedLonePairsCertified (angle : TorsionAngle) :
    P94SelectedLonePairsCertified ledger (.torsion (torsionRecord angle)) := by
  intro record equality candidate member atom lonePair
  cases equality
  simp [torsionRecord] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [frontChlorine, frontHydrogenOne, frontHydrogenTwo,
      rearChlorine, rearHydrogenOne, rearHydrogenTwo] at lonePair

theorem apSenseSupport :
    (P94ConformationEvidence.torsion apRecord : P94ReviewedEvidence).Supports
      (.torsionSense .clockwise) := by
  exact ⟨rfl, rfl, by norm_num [SignAgreesWithRotation, apRecord, torsionRecord, apAngle]⟩

theorem apClassSupport :
    (P94ConformationEvidence.torsion apRecord : P94ReviewedEvidence).Supports
      (.torsionClass .antiperiplanar) := by
  exact ⟨rfl, torsionRecord_selected apAngle, by
    norm_num [ClassifiedAs, TorsionAngle.magnitude, apRecord, torsionRecord, apAngle]⟩

theorem acSenseSupport :
    (P94ConformationEvidence.torsion acRecord : P94ReviewedEvidence).Supports
      (.torsionSense .clockwise) := by
  exact ⟨rfl, rfl, by norm_num [SignAgreesWithRotation, acRecord, torsionRecord, acAngle]⟩

theorem acClassSupport :
    (P94ConformationEvidence.torsion acRecord : P94ReviewedEvidence).Supports
      (.torsionClass .anticlinal) := by
  exact ⟨rfl, torsionRecord_selected acAngle, by
    norm_num [ClassifiedAs, TorsionAngle.magnitude, acRecord, torsionRecord, acAngle]⟩

theorem scSenseSupport :
    (P94ConformationEvidence.torsion scRecord : P94ReviewedEvidence).Supports
      (.torsionSense .clockwise) := by
  exact ⟨rfl, rfl, by norm_num [SignAgreesWithRotation, scRecord, torsionRecord, scAngle]⟩

theorem scClassSupport :
    (P94ConformationEvidence.torsion scRecord : P94ReviewedEvidence).Supports
      (.torsionClass .synclinal) := by
  exact ⟨rfl, torsionRecord_selected scAngle, by
    norm_num [ClassifiedAs, TorsionAngle.magnitude, scRecord, torsionRecord, scAngle]⟩

theorem spClassSupport :
    (P94ConformationEvidence.torsion spRecord : P94ReviewedEvidence).Supports
      (.torsionClass .synperiplanar) := by
  exact ⟨rfl, torsionRecord_selected spAngle, by
    norm_num [ClassifiedAs, TorsionAngle.magnitude, spRecord, torsionRecord, spAngle]⟩

private def apSenseEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .torsionSense .clockwise
  evidence := .torsion apRecord
  unitValid := torsionUnit_valid
  molecularRolesValid := torsionRecord_roles apAngle
  predicateClosure := .torsion apRecord
  selectedLonePairsCertified := selectedLonePairsCertified apAngle
  matchesEvidence := torsionRecord_selected apAngle
  supports := apSenseSupport

def apClassEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .torsionClass .antiperiplanar
  evidence := .torsion apRecord
  unitValid := torsionUnit_valid
  molecularRolesValid := torsionRecord_roles apAngle
  predicateClosure := .torsion apRecord
  selectedLonePairsCertified := selectedLonePairsCertified apAngle
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := apClassSupport

private def acSenseEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .torsionSense .clockwise
  evidence := .torsion acRecord
  unitValid := torsionUnit_valid
  molecularRolesValid := torsionRecord_roles acAngle
  predicateClosure := .torsion acRecord
  selectedLonePairsCertified := selectedLonePairsCertified acAngle
  matchesEvidence := torsionRecord_selected acAngle
  supports := acSenseSupport

private def acClassEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .torsionClass .anticlinal
  evidence := .torsion acRecord
  unitValid := torsionUnit_valid
  molecularRolesValid := torsionRecord_roles acAngle
  predicateClosure := .torsion acRecord
  selectedLonePairsCertified := selectedLonePairsCertified acAngle
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := acClassSupport

private def scSenseEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .torsionSense .clockwise
  evidence := .torsion scRecord
  unitValid := torsionUnit_valid
  molecularRolesValid := torsionRecord_roles scAngle
  predicateClosure := .torsion scRecord
  selectedLonePairsCertified := selectedLonePairsCertified scAngle
  matchesEvidence := torsionRecord_selected scAngle
  supports := scSenseSupport

private def scClassEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .torsionClass .synclinal
  evidence := .torsion scRecord
  unitValid := torsionUnit_valid
  molecularRolesValid := torsionRecord_roles scAngle
  predicateClosure := .torsion scRecord
  selectedLonePairsCertified := selectedLonePairsCertified scAngle
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := scClassSupport

private def gaucheEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .gauche
  evidence := .torsion scRecord
  unitValid := torsionUnit_valid
  molecularRolesValid := torsionRecord_roles scAngle
  predicateClosure := .torsion scRecord
  selectedLonePairsCertified := selectedLonePairsCertified scAngle
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := scClassSupport

private def spClassEntry : P94SourcePackageEvidenceEntry molecule ledger where
  claim := .torsionClass .synperiplanar
  evidence := .torsion spRecord
  unitValid := torsionUnit_valid
  molecularRolesValid := torsionRecord_roles spAngle
  predicateClosure := .torsion spRecord
  selectedLonePairsCertified := selectedLonePairsCertified spAngle
  matchesEvidence := by simp [P94AuthorityClaim.MatchesEvidence]
  supports := spClassSupport

private theorem ap_supportedClaim_exact (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence (.torsion apRecord))
    (supports : (P94ConformationEvidence.torsion apRecord : P94ReviewedEvidence).Supports
      claim.descriptor) :
    claim = .torsionSense .clockwise ∨ claim = .torsionClass .antiperiplanar := by
  cases claim <;> try simp [P94AuthorityClaim.MatchesEvidence] at claimMatches
  case torsionSense sense =>
    cases sense with
    | clockwise => exact Or.inl rfl
    | anticlockwise =>
        norm_num [P94AuthorityClaim.descriptor, P94ConformationEvidence.Supports,
          apRecord, torsionRecord, apAngle, SignAgreesWithRotation] at supports
  case torsionClass classification =>
    cases classification with
    | synperiplanar | synclinal | anticlinal =>
        norm_num [P94AuthorityClaim.descriptor, P94ConformationEvidence.Supports,
          apRecord, torsionRecord, apAngle, ClassifiedAs, TorsionAngle.magnitude] at supports
    | antiperiplanar => exact Or.inr rfl
  case torsionElectronicProxy classification =>
    simp [P94AuthorityClaim.TorsionSelectsElectronicProxy,
      P94AuthorityClaim.IsElectronicProxy, apRecord, torsionRecord,
      frontChlorine, rearChlorine] at claimMatches
  case gauche =>
    norm_num [P94AuthorityClaim.descriptor, P94ConformationEvidence.Supports,
      apRecord, torsionRecord, apAngle, ClassifiedAs, TorsionAngle.magnitude] at supports

private theorem ac_supportedClaim_exact (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence (.torsion acRecord))
    (supports : (P94ConformationEvidence.torsion acRecord : P94ReviewedEvidence).Supports
      claim.descriptor) :
    claim = .torsionSense .clockwise ∨ claim = .torsionClass .anticlinal := by
  cases claim <;> try simp [P94AuthorityClaim.MatchesEvidence] at claimMatches
  case torsionSense sense =>
    cases sense with
    | clockwise => exact Or.inl rfl
    | anticlockwise =>
        norm_num [P94AuthorityClaim.descriptor, P94ConformationEvidence.Supports,
          acRecord, torsionRecord, acAngle, SignAgreesWithRotation] at supports
  case torsionClass classification =>
    cases classification with
    | synperiplanar | synclinal | antiperiplanar =>
        norm_num [P94AuthorityClaim.descriptor, P94ConformationEvidence.Supports,
          acRecord, torsionRecord, acAngle, ClassifiedAs, TorsionAngle.magnitude] at supports
    | anticlinal => exact Or.inr rfl
  case torsionElectronicProxy classification =>
    simp [P94AuthorityClaim.TorsionSelectsElectronicProxy,
      P94AuthorityClaim.IsElectronicProxy, acRecord, torsionRecord,
      frontChlorine, rearChlorine] at claimMatches
  case gauche =>
    norm_num [P94AuthorityClaim.descriptor, P94ConformationEvidence.Supports,
      acRecord, torsionRecord, acAngle, ClassifiedAs, TorsionAngle.magnitude] at supports

private theorem sc_supportedClaim_exact (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence (.torsion scRecord))
    (supports : (P94ConformationEvidence.torsion scRecord : P94ReviewedEvidence).Supports
      claim.descriptor) :
    claim = .torsionSense .clockwise ∨
      claim = .torsionClass .synclinal ∨ claim = .gauche := by
  cases claim <;> try simp [P94AuthorityClaim.MatchesEvidence] at claimMatches
  case torsionSense sense =>
    cases sense with
    | clockwise => exact Or.inl rfl
    | anticlockwise =>
        norm_num [P94AuthorityClaim.descriptor, P94ConformationEvidence.Supports,
          scRecord, torsionRecord, scAngle, SignAgreesWithRotation] at supports
  case torsionClass classification =>
    cases classification with
    | synperiplanar | anticlinal | antiperiplanar =>
        norm_num [P94AuthorityClaim.descriptor, P94ConformationEvidence.Supports,
          scRecord, torsionRecord, scAngle, ClassifiedAs, TorsionAngle.magnitude] at supports
    | synclinal => exact Or.inr (Or.inl rfl)
  case torsionElectronicProxy classification =>
    simp [P94AuthorityClaim.TorsionSelectsElectronicProxy,
      P94AuthorityClaim.IsElectronicProxy, scRecord, torsionRecord,
      frontChlorine, rearChlorine] at claimMatches
  case gauche => exact Or.inr (Or.inr rfl)

private theorem sp_supportedClaim_exact (claim : P94AuthorityClaim)
    (claimMatches : claim.MatchesEvidence (.torsion spRecord))
    (supports : (P94ConformationEvidence.torsion spRecord : P94ReviewedEvidence).Supports
      claim.descriptor) :
    claim = .torsionClass .synperiplanar := by
  cases claim <;> try simp [P94AuthorityClaim.MatchesEvidence] at claimMatches
  case torsionSense sense =>
    cases sense <;>
      norm_num [P94AuthorityClaim.descriptor, P94ConformationEvidence.Supports,
        spRecord, torsionRecord, spAngle, SignAgreesWithRotation] at supports
  case torsionClass classification =>
    cases classification with
    | synperiplanar => rfl
    | synclinal | anticlinal | antiperiplanar =>
        norm_num [P94AuthorityClaim.descriptor, P94ConformationEvidence.Supports,
          spRecord, torsionRecord, spAngle, ClassifiedAs, TorsionAngle.magnitude] at supports
  case torsionElectronicProxy classification =>
    simp [P94AuthorityClaim.TorsionSelectsElectronicProxy,
      P94AuthorityClaim.IsElectronicProxy, spRecord, torsionRecord,
      frontChlorine, rearChlorine] at claimMatches
  case gauche =>
    norm_num [P94AuthorityClaim.descriptor, P94ConformationEvidence.Supports,
      spRecord, torsionRecord, spAngle, ClassifiedAs, TorsionAngle.magnitude] at supports

def sourcePackage : P94SourcePackageSchema source molecule where
  authoritativeStructureAgreement := structureAgreement
  lonePairLedger := ledger
  ledgerSource := rfl
  evidenceEntries :=
    [ apSenseEntry, apClassEntry
    , acSenseEntry, acClassEntry
    , scSenseEntry, scClassEntry, gaucheEntry
    , spClassEntry ]
  compatibleClaimsListed := by
    intro entry member claim claimMatches supports
    simp at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rcases ap_supportedClaim_exact claim claimMatches supports with rfl | rfl
      · exact ⟨apSenseEntry, by simp, rfl, rfl⟩
      · exact ⟨apClassEntry, by simp, rfl, rfl⟩
    · rcases ap_supportedClaim_exact claim claimMatches supports with rfl | rfl
      · exact ⟨apSenseEntry, by simp, rfl, rfl⟩
      · exact ⟨apClassEntry, by simp, rfl, rfl⟩
    · rcases ac_supportedClaim_exact claim claimMatches supports with rfl | rfl
      · exact ⟨acSenseEntry, by simp, rfl, rfl⟩
      · exact ⟨acClassEntry, by simp, rfl, rfl⟩
    · rcases ac_supportedClaim_exact claim claimMatches supports with rfl | rfl
      · exact ⟨acSenseEntry, by simp, rfl, rfl⟩
      · exact ⟨acClassEntry, by simp, rfl, rfl⟩
    · rcases sc_supportedClaim_exact claim claimMatches supports with rfl | rfl | rfl
      · exact ⟨scSenseEntry, by simp, rfl, rfl⟩
      · exact ⟨scClassEntry, by simp, rfl, rfl⟩
      · exact ⟨gaucheEntry, by simp, rfl, rfl⟩
    · rcases sc_supportedClaim_exact claim claimMatches supports with rfl | rfl | rfl
      · exact ⟨scSenseEntry, by simp, rfl, rfl⟩
      · exact ⟨scClassEntry, by simp, rfl, rfl⟩
      · exact ⟨gaucheEntry, by simp, rfl, rfl⟩
    · rcases sc_supportedClaim_exact claim claimMatches supports with rfl | rfl | rfl
      · exact ⟨scSenseEntry, by simp, rfl, rfl⟩
      · exact ⟨scClassEntry, by simp, rfl, rfl⟩
      · exact ⟨gaucheEntry, by simp, rfl, rfl⟩
    · have claimExact := sp_supportedClaim_exact claim claimMatches supports
      subst claim
      exact ⟨spClassEntry, by simp, rfl, rfl⟩
  inOutCoordinatePairs := []

@[simp] theorem source_package_claims_exact :
    sourcePackage.evidenceEntries.map P94SourcePackageEvidenceEntry.claim =
      [ .torsionSense .clockwise, .torsionClass .antiperiplanar
      , .torsionSense .clockwise, .torsionClass .anticlinal
      , .torsionSense .clockwise, .torsionClass .synclinal, .gauche
      , .torsionClass .synperiplanar ] := by
  rfl

@[simp] theorem source_package_clauses_exact :
    sourcePackage.evidenceEntries.map (fun entry => entry.claim.clause) =
      [ .torsionAngle, .torsionAngle, .torsionAngle, .torsionAngle
      , .torsionAngle, .torsionAngle, .eclipsedStaggeredGauche
      , .torsionAngle ] := by
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
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [bond]

end HalogenSpecialization

def frozenRecord : P94FrozenPackageRecord where
  source := HalogenSpecialization.source
  molecule := HalogenSpecialization.molecule
  package := HalogenSpecialization.sourcePackage
  normalizationReady := HalogenSpecialization.normalizationReady

@[simp] theorem frozen_record_exact :
    frozenRecord.source = HalogenSpecialization.source ∧
      frozenRecord.molecule = HalogenSpecialization.molecule ∧
        frozenRecord.package = HalogenSpecialization.sourcePackage := by
  exact ⟨rfl, rfl, rfl⟩

def distinguishedEntry : P94FrozenDistinguishedEntry where
  record := frozenRecord
  entry := HalogenSpecialization.apClassEntry

@[simp] theorem distinguished_entry_exact :
    distinguishedEntry.entry.claim = .torsionClass .antiperiplanar ∧
      distinguishedEntry.entry.claim.clause = .torsionAngle ∧
        distinguishedEntry.entry ∈ distinguishedEntry.record.package.evidenceEntries := by
  constructor
  · rfl
  · constructor
    · rfl
    · simp [distinguishedEntry, frozenRecord, HalogenSpecialization.sourcePackage]

structure FrozenSourceTranscription where
  artifactSha256 : String
  illustrationBlocks : List P94SourceAuditLedger.IllustrationBlock
  boundaries : List TorsionClassBoundary
  halogenClasses : List ConformationalClass
  criteria : List SelectionCriterion
  criterionExamples : List SelectionExampleRecord
  packageRecord : P94FrozenPackageRecord

def frozenSourceTranscription : FrozenSourceTranscription where
  artifactSha256 := sourceArtifactSha256
  illustrationBlocks := sourceIllustrationBlocks
  boundaries := classBoundaries
  halogenClasses := halogenExampleClasses
  criteria := selectionCriteria
  criterionExamples := selectionExampleLedger
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

end P94TorsionAngleSourceRecord
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P94TorsionAngleSourceRecord.source_illustration_bindings_exact
assert_kernel_only
  TetraStereo.OneCenter.P94TorsionAngleSourceRecord.class_boundaries_exact
assert_kernel_only
  TetraStereo.OneCenter.P94TorsionAngleSourceRecord.inclusive_class_boundaries_exact
assert_kernel_only
  TetraStereo.OneCenter.P94TorsionAngleSourceRecord.selection_example_ledger_exact
assert_kernel_only
  TetraStereo.OneCenter.P94TorsionAngleSourceRecord.HalogenSpecialization.torsionUnit_valid
assert_kernel_only
  TetraStereo.OneCenter.P94TorsionAngleSourceRecord.HalogenSpecialization.records_selected_exact
assert_kernel_only
  TetraStereo.OneCenter.P94TorsionAngleSourceRecord.HalogenSpecialization.source_package_claims_exact
assert_kernel_only
  TetraStereo.OneCenter.P94TorsionAngleSourceRecord.HalogenSpecialization.normalizationReady
assert_kernel_only
  TetraStereo.OneCenter.P94TorsionAngleSourceRecord.distinguished_entry_exact
assert_kernel_only
  TetraStereo.OneCenter.P94TorsionAngleSourceRecord.current_independent_source_review_issued
