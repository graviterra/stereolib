import TetraStereo.OneCenter.CertificateExport
import TetraStereo.OneCenter.StereochemicalElements

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

/-!
  Proof-carrying CIP validation fixtures.

  This module is the start of the regression-suite boundary.  It captures official sequence-rule
  edge cases as Lean values, each carrying a checked theorem artifact.  External suites such as
  Hanson--Mayfield can be mapped into the same `CIPValidationFixture` shape once their host parser
  bridge emits `RawMolecule` packets and expected outcomes.
-/

open Prod.Lex

/-! ### Fixture metadata -/

/-- Provenance bucket for a stereochemical validation fixture. -/
inductive CIPValidationSuite where
  | iupacP92CoreRules
  | officialCIPRegression
  | hansonMayfieldExternal
  | hansonMayfieldPlaceholder
  | localTetraStereo
  deriving DecidableEq, Repr

/-- Fixture class. -/
inductive CIPValidationFixtureKind where
  | rule1aAtomicNumber
  | rule2AtomicMass
  | frontierExhaustion
  | rule3DoubleBondGeometry
  | rule4aStereogenicUnitKind
  | rule4bLikeUnlikeDescriptorPairs
  | rule4cPseudoasymmetricDescriptor
  | rule5EnantiomorphicDescriptor
  | noncenterDetectorRegistration
  | externalSuiteIngestion
  | safeTieRefusal
  deriving DecidableEq, Repr

/-! ### External validation-suite ingestion -/

/-- Expected-output shape for an externally sourced validation case. -/
inductive ExternalValidationExpected where
  | comparison (expected : Ordering)
  | descriptorLabel (label : String)
  | refusal (reason : String)
  deriving DecidableEq, Repr

/-- Metadata for a validation case before it has been converted into a checked Lean fixture. -/
structure ExternalValidationCaseSpec where
  id : String
  name : String
  suite : CIPValidationSuite
  kind : CIPValidationFixtureKind
  source : String
  format : ChemistryImportFormat
  expected : ExternalValidationExpected
  payloadHash? : Option String := none
  notes : List String := []
  deriving DecidableEq, Repr

/-- A checked stereochemical validation fixture. -/
structure CIPValidationFixture where
  id : String
  name : String
  suite : CIPValidationSuite
  kind : CIPValidationFixtureKind
  source : String
  expected : Ordering
  artifact : LeanCertificateArtifact

namespace CIPValidationFixture

/-- Fixture claim. -/
def claim (fixture : CIPValidationFixture) : Prop :=
  fixture.artifact.claim

/-- Fixture proof. -/
theorem checked (fixture : CIPValidationFixture) : fixture.claim :=
  fixture.artifact.proof

end CIPValidationFixture

/-- A batch of validation fixtures. -/
structure CIPValidationFixtureBatch where
  name : String
  fixtures : List CIPValidationFixture

namespace CIPValidationFixtureBatch

/-- All fixture claims in a validation batch hold. -/
def AllClaims (batch : CIPValidationFixtureBatch) : Prop :=
  ∀ fixture, fixture ∈ batch.fixtures → fixture.claim

/-- Convert a validation fixture batch to the generic certificate batch. -/
def toCertificateBatch (batch : CIPValidationFixtureBatch) : LeanCertificateBatch where
  artifacts := batch.fixtures.map fun fixture => fixture.artifact

/-- Every fixture in the batch is Lean-checked. -/
theorem checked (batch : CIPValidationFixtureBatch) : batch.AllClaims := by
  intro fixture _hmem
  exact fixture.checked

/-- The generic certificate batch obtained from a validation batch is also checked. -/
theorem certificateBatch_checked (batch : CIPValidationFixtureBatch) :
    batch.toCertificateBatch.AllClaims :=
  batch.toCertificateBatch.checked

end CIPValidationFixtureBatch

/-- One externally sourced validation case after importer/translator processing.  A checked
fixture is present only when the case has reached the proof-carrying artifact boundary. -/
structure ExternalValidationCaseImport where
  spec : ExternalValidationCaseSpec
  checkedFixture? : Option CIPValidationFixture := none

/-- A batch of external validation cases at the ingestion boundary. -/
structure ExternalValidationSuiteIngestion where
  name : String
  cases : List ExternalValidationCaseImport

namespace ExternalValidationSuiteIngestion

/-- Checked fixtures that have already crossed the external-suite ingestion boundary. -/
def checkedFixtures (ingestion : ExternalValidationSuiteIngestion) : List CIPValidationFixture :=
  ingestion.cases.filterMap fun entry => entry.checkedFixture?


def pendingSpecs (ingestion : ExternalValidationSuiteIngestion) : List ExternalValidationCaseSpec :=
  ingestion.cases.filterMap fun entry =>
    match entry.checkedFixture? with
    | some _ => none
    | none => some entry.spec

/-- Convert checked imported cases into the ordinary proof-carrying fixture batch. -/
def checkedFixtureBatch (ingestion : ExternalValidationSuiteIngestion) :
    CIPValidationFixtureBatch where
  name := ingestion.name ++ " checked fixtures"
  fixtures := ingestion.checkedFixtures

/-- All checked imported cases carry Lean-checked claims. -/
theorem checked (ingestion : ExternalValidationSuiteIngestion) :
    ingestion.checkedFixtureBatch.AllClaims :=
  ingestion.checkedFixtureBatch.checked

end ExternalValidationSuiteIngestion

/-! ### Trace fixtures -/

/-- Compact atom-label constructor for Rule 1/2 key fixtures. -/
def atomLabel (atomicNumber isotopeMass : ℕ) : MoleculeGraph.AtomLabel :=
  toLex (atomicNumber, isotopeMass)

/-- A tied graph key forces the descriptor-rich official rules to fire. -/
def tiedKey : List MoleculeGraph.AtomLabel :=
  []

/-- Single-step key-comparison fixture certificate. -/
def keyComparisonCertificate (left right : List MoleculeGraph.AtomLabel) :
    CIPTraceCertificate :=
  CIPRuleEngine.compareKeyCertificate left right

/-- Official context fixture certificate, used when ordinary graph keys tie. -/
def officialContextCertificate
    (left right : CIPRuleEngine.OfficialLigandRuleContext) :
    CIPTraceCertificate :=
  CIPRuleEngine.compareKeyThenOfficialCertificate tiedKey tiedKey left right

/-- Generic trace-validation fixture constructor. -/
def traceValidationFixture (id name source theoremName certificateExpr expectedExpr : String)
    (suite : CIPValidationSuite) (kind : CIPValidationFixtureKind)
    (certificate : CIPTraceCertificate) (expected : Ordering)
    (h : TraceOutcomeCertificateClaim certificate expected) :
    CIPValidationFixture where
  id := id
  name := name
  suite := suite
  kind := kind
  source := source
  expected := expected
  artifact :=
    let base :=
      compileTraceOutcomeCertificate theoremName certificateExpr expectedExpr "  rfl" certificate
        expected h
    { base with
      kind := LeanCertificateKind.validationFixture
      title := name
      theoremExport :=
        { base.theoremExport with
          imports := ["TetraStereo.OneCenter.CIPValidationFixtures"]
          namespacePath := ["TetraStereo", "OneCenter", "GeneratedFixtures"] } }

/-! ### Core official-CIP edge fixtures -/

def rule1AtomicNumberCertificate : CIPTraceCertificate :=
  keyComparisonCertificate [atomLabel 8 0] [atomLabel 6 0]

theorem rule1AtomicNumberCertificate_outcome :
    TraceOutcomeCertificateClaim rule1AtomicNumberCertificate Ordering.gt := by
  rfl

def rule1AtomicNumberFixture : CIPValidationFixture :=
  traceValidationFixture
    "iupac-p92-rule1a-o-before-c"
    "Rule 1a: oxygen outranks carbon"
    "IUPAC P-92.2.1"
    "rule1_atomic_number_o_over_c"
    "rule1AtomicNumberCertificate"
    "Ordering.gt"
    CIPValidationSuite.iupacP92CoreRules
    CIPValidationFixtureKind.rule1aAtomicNumber
    rule1AtomicNumberCertificate
    Ordering.gt
    rule1AtomicNumberCertificate_outcome

def rule2AtomicMassCertificate : CIPTraceCertificate :=
  keyComparisonCertificate [atomLabel 6 13] [atomLabel 6 12]

theorem rule2AtomicMassCertificate_outcome :
    TraceOutcomeCertificateClaim rule2AtomicMassCertificate Ordering.gt := by
  rfl

def rule2AtomicMassFixture : CIPValidationFixture :=
  traceValidationFixture
    "iupac-p92-rule2-c13-before-c12"
    "Rule 2: carbon-13 outranks carbon-12"
    "IUPAC P-92.3"
    "rule2_atomic_mass_c13_over_c12"
    "rule2AtomicMassCertificate"
    "Ordering.gt"
    CIPValidationSuite.iupacP92CoreRules
    CIPValidationFixtureKind.rule2AtomicMass
    rule2AtomicMassCertificate
    Ordering.gt
    rule2AtomicMassCertificate_outcome

def frontierExhaustionCertificate : CIPTraceCertificate :=
  keyComparisonCertificate [atomLabel 6 0, atomLabel 1 0] [atomLabel 6 0]

theorem frontierExhaustionCertificate_outcome :
    TraceOutcomeCertificateClaim frontierExhaustionCertificate Ordering.gt := by
  rfl

def frontierExhaustionFixture : CIPValidationFixture :=
  traceValidationFixture
    "tetrastereo-frontier-longer-after-tie"
    "Frontier exhaustion: longer tied-prefix key outranks exhausted key"
    "TetraStereo key-regression"
    "frontier_exhaustion_longer_after_tie"
    "frontierExhaustionCertificate"
    "Ordering.gt"
    CIPValidationSuite.localTetraStereo
    CIPValidationFixtureKind.frontierExhaustion
    frontierExhaustionCertificate
    Ordering.gt
    frontierExhaustionCertificate_outcome

def rule3SeqCisSeqTransCertificate : CIPTraceCertificate :=
  officialContextCertificate
    (CIPRuleEngine.OfficialLigandRuleContext.ofRule3Geometry OfficialRule3Geometry.seqcis)
    (CIPRuleEngine.OfficialLigandRuleContext.ofRule3Geometry OfficialRule3Geometry.seqtrans)

theorem rule3SeqCisSeqTransCertificate_outcome :
    TraceOutcomeCertificateClaim rule3SeqCisSeqTransCertificate Ordering.gt := by
  rfl

def rule3SeqCisSeqTransFixture : CIPValidationFixture :=
  traceValidationFixture
    "iupac-p92-rule3-seqcis-before-seqtrans"
    "Rule 3: seqcis outranks seqtrans"
    "IUPAC P-92.4"
    "rule3_seqcis_over_seqtrans"
    "rule3SeqCisSeqTransCertificate"
    "Ordering.gt"
    CIPValidationSuite.iupacP92CoreRules
    CIPValidationFixtureKind.rule3DoubleBondGeometry
    rule3SeqCisSeqTransCertificate
    Ordering.gt
    rule3SeqCisSeqTransCertificate_outcome

def rule4aChiralPseudoCertificate : CIPTraceCertificate :=
  officialContextCertificate
    (CIPRuleEngine.OfficialLigandRuleContext.ofRule4aKind
      OfficialStereogenicUnitKind.chiral)
    (CIPRuleEngine.OfficialLigandRuleContext.ofRule4aKind
      OfficialStereogenicUnitKind.pseudoasymmetric)

theorem rule4aChiralPseudoCertificate_outcome :
    TraceOutcomeCertificateClaim rule4aChiralPseudoCertificate Ordering.gt := by
  rfl

def rule4aChiralPseudoFixture : CIPValidationFixture :=
  traceValidationFixture
    "iupac-p92-rule4a-chiral-before-pseudo"
    "Rule 4a: chiral unit outranks pseudoasymmetric unit"
    "IUPAC P-92.5.1"
    "rule4a_chiral_over_pseudo"
    "rule4aChiralPseudoCertificate"
    "Ordering.gt"
    CIPValidationSuite.iupacP92CoreRules
    CIPValidationFixtureKind.rule4aStereogenicUnitKind
    rule4aChiralPseudoCertificate
    Ordering.gt
    rule4aChiralPseudoCertificate_outcome

def rule4bLikeUnlikeCertificate : CIPTraceCertificate :=
  officialContextCertificate
    (CIPRuleEngine.OfficialLigandRuleContext.ofRule4bPair OfficialDescriptorPairKind.like)
    (CIPRuleEngine.OfficialLigandRuleContext.ofRule4bPair OfficialDescriptorPairKind.unlike)

theorem rule4bLikeUnlikeCertificate_outcome :
    TraceOutcomeCertificateClaim rule4bLikeUnlikeCertificate Ordering.gt := by
  rfl

def rule4bLikeUnlikeFixture : CIPValidationFixture :=
  traceValidationFixture
    "iupac-p92-rule4b-like-before-unlike"
    "Rule 4b: like descriptor pair outranks unlike pair"
    "IUPAC P-92.5.2"
    "rule4b_like_over_unlike"
    "rule4bLikeUnlikeCertificate"
    "Ordering.gt"
    CIPValidationSuite.iupacP92CoreRules
    CIPValidationFixtureKind.rule4bLikeUnlikeDescriptorPairs
    rule4bLikeUnlikeCertificate
    Ordering.gt
    rule4bLikeUnlikeCertificate_outcome

def rule4cROverSCertificate : CIPTraceCertificate :=
  officialContextCertificate
    (CIPRuleEngine.OfficialLigandRuleContext.ofRule4cDescriptor
      OfficialPseudoasymmetricDescriptor.r)
    (CIPRuleEngine.OfficialLigandRuleContext.ofRule4cDescriptor
      OfficialPseudoasymmetricDescriptor.s)

theorem rule4cROverSCertificate_outcome :
    TraceOutcomeCertificateClaim rule4cROverSCertificate Ordering.gt := by
  rfl

def rule4cROverSFixture : CIPValidationFixture :=
  traceValidationFixture
    "iupac-p92-rule4c-r-before-s"
    "Rule 4c: lowercase r outranks lowercase s"
    "IUPAC P-92.5.3"
    "rule4c_r_over_s"
    "rule4cROverSCertificate"
    "Ordering.gt"
    CIPValidationSuite.iupacP92CoreRules
    CIPValidationFixtureKind.rule4cPseudoasymmetricDescriptor
    rule4cROverSCertificate
    Ordering.gt
    rule4cROverSCertificate_outcome

def rule4cMOverPCertificate : CIPTraceCertificate :=
  officialContextCertificate
    (CIPRuleEngine.OfficialLigandRuleContext.ofRule4cDescriptor
      OfficialPseudoasymmetricDescriptor.m)
    (CIPRuleEngine.OfficialLigandRuleContext.ofRule4cDescriptor
      OfficialPseudoasymmetricDescriptor.p)

theorem rule4cMOverPCertificate_outcome :
    TraceOutcomeCertificateClaim rule4cMOverPCertificate Ordering.gt := by
  rfl

def rule4cMOverPFixture : CIPValidationFixture :=
  traceValidationFixture
    "iupac-p92-rule4c-m-before-p"
    "Rule 4c: lowercase m outranks lowercase p"
    "IUPAC P-92.5.3"
    "rule4c_m_over_p"
    "rule4cMOverPCertificate"
    "Ordering.gt"
    CIPValidationSuite.iupacP92CoreRules
    CIPValidationFixtureKind.rule4cPseudoasymmetricDescriptor
    rule4cMOverPCertificate
    Ordering.gt
    rule4cMOverPCertificate_outcome

def rule4cCrossFamilyTieCertificate : CIPTraceCertificate :=
  officialContextCertificate
    (CIPRuleEngine.OfficialLigandRuleContext.ofRule4cDescriptor
      OfficialPseudoasymmetricDescriptor.r)
    (CIPRuleEngine.OfficialLigandRuleContext.ofRule4cDescriptor
      OfficialPseudoasymmetricDescriptor.m)

theorem rule4cCrossFamilyTieCertificate_outcome :
    TraceOutcomeCertificateClaim rule4cCrossFamilyTieCertificate Ordering.eq := by
  rfl

def rule4cCrossFamilyTieFixture : CIPValidationFixture :=
  traceValidationFixture
    "iupac-p92-rule4c-cross-family-safe-tie"
    "Rule 4c: cross-family pseudoasymmetric descriptors safely tie"
    "IUPAC P-92.5.3 boundary"
    "rule4c_cross_family_tie"
    "rule4cCrossFamilyTieCertificate"
    "Ordering.eq"
    CIPValidationSuite.officialCIPRegression
    CIPValidationFixtureKind.safeTieRefusal
    rule4cCrossFamilyTieCertificate
    Ordering.eq
    rule4cCrossFamilyTieCertificate_outcome

def rule5ROverSCertificate : CIPTraceCertificate :=
  officialContextCertificate
    (CIPRuleEngine.OfficialLigandRuleContext.ofRS RS.R)
    (CIPRuleEngine.OfficialLigandRuleContext.ofRS RS.S)

theorem rule5ROverSCertificate_outcome :
    TraceOutcomeCertificateClaim rule5ROverSCertificate Ordering.gt := by
  rfl

def rule5ROverSFixture : CIPValidationFixture :=
  traceValidationFixture
    "iupac-p92-rule5-r-before-s"
    "Rule 5: R outranks S"
    "IUPAC P-92.6"
    "rule5_R_over_S"
    "rule5ROverSCertificate"
    "Ordering.gt"
    CIPValidationSuite.iupacP92CoreRules
    CIPValidationFixtureKind.rule5EnantiomorphicDescriptor
    rule5ROverSCertificate
    Ordering.gt
    rule5ROverSCertificate_outcome

def rule5MOverPCertificate : CIPTraceCertificate :=
  officialContextCertificate
    (CIPRuleEngine.OfficialLigandRuleContext.ofRule5Descriptor
      OfficialRule5Descriptor.descriptorM)
    (CIPRuleEngine.OfficialLigandRuleContext.ofRule5Descriptor
      OfficialRule5Descriptor.descriptorP)

theorem rule5MOverPCertificate_outcome :
    TraceOutcomeCertificateClaim rule5MOverPCertificate Ordering.gt := by
  rfl

def rule5MOverPFixture : CIPValidationFixture :=
  traceValidationFixture
    "iupac-p92-rule5-m-before-p"
    "Rule 5: M outranks P"
    "IUPAC P-92.6"
    "rule5_M_over_P"
    "rule5MOverPCertificate"
    "Ordering.gt"
    CIPValidationSuite.iupacP92CoreRules
    CIPValidationFixtureKind.rule5EnantiomorphicDescriptor
    rule5MOverPCertificate
    Ordering.gt
    rule5MOverPCertificate_outcome

def rule5SeqCisSeqTransCertificate : CIPTraceCertificate :=
  officialContextCertificate
    (CIPRuleEngine.OfficialLigandRuleContext.ofRule5Descriptor
      OfficialRule5Descriptor.descriptorSeqCis)
    (CIPRuleEngine.OfficialLigandRuleContext.ofRule5Descriptor
      OfficialRule5Descriptor.descriptorSeqTrans)

theorem rule5SeqCisSeqTransCertificate_outcome :
    TraceOutcomeCertificateClaim rule5SeqCisSeqTransCertificate Ordering.gt := by
  rfl

def rule5SeqCisSeqTransFixture : CIPValidationFixture :=
  traceValidationFixture
    "iupac-p92-rule5-seqcis-before-seqtrans"
    "Rule 5: seqCis outranks seqTrans"
    "IUPAC P-92.6"
    "rule5_seqcis_over_seqtrans"
    "rule5SeqCisSeqTransCertificate"
    "Ordering.gt"
    CIPValidationSuite.iupacP92CoreRules
    CIPValidationFixtureKind.rule5EnantiomorphicDescriptor
    rule5SeqCisSeqTransCertificate
    Ordering.gt
    rule5SeqCisSeqTransCertificate_outcome

def rule5AuxiliaryROverSCertificate : CIPTraceCertificate :=
  officialContextCertificate
    (CIPRuleEngine.OfficialLigandRuleContext.ofRule5Descriptor
      (OfficialRule5Descriptor.asAuxiliary OfficialRule5Descriptor.descriptorR))
    (CIPRuleEngine.OfficialLigandRuleContext.ofRule5Descriptor
      (OfficialRule5Descriptor.asAuxiliary OfficialRule5Descriptor.descriptorS))

theorem rule5AuxiliaryROverSCertificate_outcome :
    TraceOutcomeCertificateClaim rule5AuxiliaryROverSCertificate Ordering.gt := by
  rfl

def rule5AuxiliaryROverSFixture : CIPValidationFixture :=
  traceValidationFixture
    "iupac-p92-rule5-auxiliary-r-before-s"
    "Rule 5: auxiliary R outranks auxiliary S"
    "IUPAC P-92.6 auxiliary descriptor layer"
    "rule5_auxiliary_R_over_S"
    "rule5AuxiliaryROverSCertificate"
    "Ordering.gt"
    CIPValidationSuite.officialCIPRegression
    CIPValidationFixtureKind.rule5EnantiomorphicDescriptor
    rule5AuxiliaryROverSCertificate
    Ordering.gt
    rule5AuxiliaryROverSCertificate_outcome

def emptyContextSafeTieCertificate : CIPTraceCertificate :=
  officialContextCertificate
    CIPRuleEngine.OfficialLigandRuleContext.empty
    CIPRuleEngine.OfficialLigandRuleContext.empty

theorem emptyContextSafeTieCertificate_outcome :
    TraceOutcomeCertificateClaim emptyContextSafeTieCertificate Ordering.eq := by
  rfl

def emptyContextSafeTieFixture : CIPValidationFixture :=
  traceValidationFixture
    "official-empty-context-safe-tie"
    "Missing official descriptor context safely ties"
    "Official-context safety regression"
    "empty_context_safe_tie"
    "emptyContextSafeTieCertificate"
    "Ordering.eq"
    CIPValidationSuite.officialCIPRegression
    CIPValidationFixtureKind.safeTieRefusal
    emptyContextSafeTieCertificate
    Ordering.eq
    emptyContextSafeTieCertificate_outcome

/-- Core checked fixture suite for official CIP edge behavior currently represented in Lean. -/
def officialCIPEdgeFixtures : List CIPValidationFixture :=
  [ rule1AtomicNumberFixture
  , rule2AtomicMassFixture
  , frontierExhaustionFixture
  , rule3SeqCisSeqTransFixture
  , rule4aChiralPseudoFixture
  , rule4bLikeUnlikeFixture
  , rule4cROverSFixture
  , rule4cMOverPFixture
  , rule4cCrossFamilyTieFixture
  , rule5ROverSFixture
  , rule5MOverPFixture
  , rule5SeqCisSeqTransFixture
  , rule5AuxiliaryROverSFixture
  , emptyContextSafeTieFixture
  ]

def officialCIPEdgeFixtureBatch : CIPValidationFixtureBatch where
  name := "Official CIP edge fixtures"
  fixtures := officialCIPEdgeFixtures

theorem officialCIPEdgeFixtureBatch_checked :
    officialCIPEdgeFixtureBatch.AllClaims :=
  officialCIPEdgeFixtureBatch.checked

@[simp] theorem officialCIPEdgeFixtures_length :
    officialCIPEdgeFixtures.length = 14 :=
  rfl

/-! ### External-suite ingestion seed -/

/-- External-style spec for a checked Rule-3 comparison case. -/
def externalRule3SeqCisSeqTransSpec : ExternalValidationCaseSpec where
  id := "external-rule3-seqcis-before-seqtrans"
  name := "External Rule 3: seqcis outranks seqtrans"
  suite := CIPValidationSuite.officialCIPRegression
  kind := CIPValidationFixtureKind.externalSuiteIngestion
  source := "external validation-suite ingestion smoke case"
  format := ChemistryImportFormat.rawMolecule
  expected := ExternalValidationExpected.comparison Ordering.gt
  notes := ["Demonstrates how an externally sourced expected comparison becomes a checked fixture."]

/-- Checked imported version of the external-style Rule-3 case. -/
def externalRule3SeqCisSeqTransImport : ExternalValidationCaseImport where
  spec := externalRule3SeqCisSeqTransSpec
  checkedFixture? := some rule3SeqCisSeqTransFixture


def pendingHansonMayfieldAtropisomerSpec : ExternalValidationCaseSpec where
  id := "hm-pending-atropisomer-axis"
  name := "Pending external atropisomeric axis descriptor"
  suite := CIPValidationSuite.hansonMayfieldExternal
  kind := CIPValidationFixtureKind.externalSuiteIngestion
  source := "Hanson--Mayfield-style external benchmark slot"
  format := ChemistryImportFormat.rdkitJSON
  expected := ExternalValidationExpected.descriptorLabel "axial descriptor"
  notes :=
    [ "Pending until the host bridge supplies molecule coordinates/axis perception."
    , "Tracked explicitly so external-suite coverage cannot be mistaken for checked Lean proof."
    ]


def externalValidationIngestionSeed : ExternalValidationSuiteIngestion where
  name := "External validation ingestion seed"
  cases :=
    [ externalRule3SeqCisSeqTransImport
    , { spec := pendingHansonMayfieldAtropisomerSpec, checkedFixture? := none }
    ]

theorem externalValidationIngestionSeed_checked :
    externalValidationIngestionSeed.checkedFixtureBatch.AllClaims :=
  externalValidationIngestionSeed.checked

@[simp] theorem externalValidationIngestionSeed_checkedFixtures_length :
    externalValidationIngestionSeed.checkedFixtures.length = 1 :=
  rfl

@[simp] theorem externalValidationIngestionSeed_pendingSpecs_length :
    externalValidationIngestionSeed.pendingSpecs.length = 1 :=
  rfl

end
end OneCenter
end TetraStereo
