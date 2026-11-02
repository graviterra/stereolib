import TetraStereo.OneCenter.ChemistryImport
import TetraStereo.OneCenter.OfficialCIPEngine

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

/-!
  Certificate export boundary.

  This module is the first host-facing certificate compiler layer.  It does not try to serialize
  arbitrary chemistry by magic inside Lean.  Instead, it names the contract used by a host program:

  * decode a host molecule through `ChemistryImport`,
  * run an engine step that already returns Lean-checkable data,
  * package the resulting proposition plus proof as a `LeanCertificateArtifact`,
  * render a theorem skeleton that a host exporter can write to a `.lean` file.

  The crucial point is that every artifact stores `claim : Prop` together with `proof : claim`.
  The string export is the host-facing file shape; the artifact itself is the checked Lean object.
-/

/-! ### Lean source fragments -/

/-- Join lines with newline separators. -/
def joinLines : List String → String
  | [] => ""
  | line :: [] => line
  | line :: rest => line ++ "\n" ++ joinLines rest

/-- A rendered theorem target for a host-generated Lean certificate file. -/
structure LeanTheoremExport where
  imports : List String
  options : List String := []
  namespacePath : List String := ["TetraStereo", "Generated"]
  theoremName : String
  statement : String
  proofTerm : String
  deriving Repr

namespace LeanTheoremExport

/-- Render import lines. -/
def importLines (artifact : LeanTheoremExport) : List String :=
  artifact.imports.map fun moduleName => "import " ++ moduleName

/-- Render namespace-open lines. -/
def namespaceOpenLines (artifact : LeanTheoremExport) : List String :=
  artifact.namespacePath.map fun namespaceName => "namespace " ++ namespaceName

/-- Render namespace-close lines. -/
def namespaceCloseLines (artifact : LeanTheoremExport) : List String :=
  artifact.namespacePath.reverse.map fun namespaceName => "end " ++ namespaceName

/-- Render the theorem declaration. -/
def theoremLines (artifact : LeanTheoremExport) : List String :=
  [ "theorem " ++ artifact.theoremName ++ " : " ++ artifact.statement ++ " := by"
  , artifact.proofTerm
  ]

/-- Render the full Lean source text for the certificate theorem. -/
def source (artifact : LeanTheoremExport) : String :=
  joinLines
    (artifact.importLines ++ [""] ++ artifact.options ++ [""] ++ artifact.namespaceOpenLines ++ [""] ++
      artifact.theoremLines ++ [""] ++ artifact.namespaceCloseLines)

end LeanTheoremExport

/-! ### Checked certificate artifacts -/

/-- Certificate classes emitted by the host-facing compiler. -/
inductive LeanCertificateKind where
  | importNormalization
  | importRefusal
  | traceOutcome
  | officialLigandComparison
  | rsAssignment
  | rsRefusal
  | stereoClaim
  | stereoClaimRefusal
  | validationFixture
  deriving DecidableEq, Repr





structure LeanCertificateArtifact where
  kind : LeanCertificateKind
  title : String
  theoremExport : LeanTheoremExport
  source? : Option ChemistryImportSource := none
  trust? : Option ChemistryImportTrust := none
  boundary? : Option ChemistryNormalizationBoundaryReport := none
  claim : Prop
  proof : claim

namespace LeanCertificateArtifact

/-- Render the theorem source planned for this certificate. -/
def source (artifact : LeanCertificateArtifact) : String :=
  artifact.theoremExport.source

/-- The checked theorem carried by the artifact. -/
theorem checked (artifact : LeanCertificateArtifact) : artifact.claim :=
  artifact.proof

end LeanCertificateArtifact

/-- A batch of certificate artifacts. -/
structure LeanCertificateBatch where
  artifacts : List LeanCertificateArtifact

namespace LeanCertificateBatch

/-- All claims in a certificate batch hold. -/
def AllClaims (batch : LeanCertificateBatch) : Prop :=
  ∀ artifact, artifact ∈ batch.artifacts → artifact.claim

/-- A batch is checked exactly because every artifact carries its own proof. -/
theorem checked (batch : LeanCertificateBatch) : batch.AllClaims := by
  intro artifact _hmem
  exact artifact.proof

end LeanCertificateBatch

/-! ### Import-normalization certificates -/

/-- Claim certified for a predecoded host molecule entering through an import packet. -/
def RawImportCertificateClaim (packet : ExternalRawMoleculePacket) : Prop :=
  let result := importExternalRawMoleculePacket packet
  result.source = packet.source ∧
    result.trust = packet.trust ∧
    result.raw = packet.raw ∧
    result.normalized.policy = packet.policy ∧
    result.normalized.boundary = ChemistryNormalizationBoundaryReport.ofPolicy packet.policy

/-- Every packet imported through the shared boundary satisfies its packet-normalization claim. -/
theorem rawImportCertificateClaim_holds (packet : ExternalRawMoleculePacket) :
    RawImportCertificateClaim packet := by
  simp [RawImportCertificateClaim, importExternalRawMoleculePacket, normalizeRawMoleculeWithPolicy]



def rawImportCertificateTheoremExport (packetDefName theoremName : String) :
    LeanTheoremExport where
  imports := ["TetraStereo.OneCenter.CertificateExport"]
  theoremName := theoremName
  statement := "TetraStereo.OneCenter.RawImportCertificateClaim " ++ packetDefName
  proofTerm := "  exact TetraStereo.OneCenter.rawImportCertificateClaim_holds " ++ packetDefName

/-- Compile a predecoded host molecule packet into a checked import-normalization artifact. -/
def compileRawImportCertificate (packet : ExternalRawMoleculePacket)
    (packetDefName theoremName : String) : LeanCertificateArtifact where
  kind := LeanCertificateKind.importNormalization
  title := "Host molecule import normalization"
  theoremExport := rawImportCertificateTheoremExport packetDefName theoremName
  source? := some packet.source
  trust? := some packet.trust
  boundary? := some (ChemistryNormalizationBoundaryReport.ofPolicy packet.policy)
  claim := RawImportCertificateClaim packet
  proof := rawImportCertificateClaim_holds packet

/-- Host-facing input for the import-normalization compiler. -/
structure HostMoleculeCertificateInput where
  packet : ExternalRawMoleculePacket
  packetDefName : String
  theoremName : String

/-- Compile host molecule input into a checked import-normalization certificate. -/
def compileHostMoleculeImportCertificate (input : HostMoleculeCertificateInput) :
    LeanCertificateArtifact :=
  compileRawImportCertificate input.packet input.packetDefName input.theoremName

/-! ### Engine-result certificates -/

/-- Generic claim that a proof-carrying CIP trace certificate has a concrete outcome. -/
def TraceOutcomeCertificateClaim (certificate : CIPTraceCertificate) (expected : Ordering) :
    Prop :=
  certificate.outcome = expected


def traceOutcomeTheoremExport (certificateExpr expectedExpr theoremName proofTerm : String) :
    LeanTheoremExport where
  imports := ["TetraStereo.OneCenter.CertificateExport"]
  theoremName := theoremName
  statement :=
    "TetraStereo.OneCenter.TraceOutcomeCertificateClaim " ++ certificateExpr ++ " " ++
      expectedExpr
  proofTerm := proofTerm

/-- Compile a checked CIP trace outcome into a theorem artifact. -/
def compileTraceOutcomeCertificate (theoremName certificateExpr expectedExpr proofTerm : String)
    (certificate : CIPTraceCertificate) (expected : Ordering)
    (h : TraceOutcomeCertificateClaim certificate expected) :
    LeanCertificateArtifact where
  kind := LeanCertificateKind.traceOutcome
  title := "CIP trace outcome"
  theoremExport := traceOutcomeTheoremExport certificateExpr expectedExpr theoremName proofTerm
  claim := TraceOutcomeCertificateClaim certificate expected
  proof := h

/-- Claim that an official one-center ligand comparison has a concrete outcome. -/
def OfficialComparisonCertificateClaim {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (i j : Fin 4) (expected : Ordering) : Prop :=
  (m.cipOfficialCompare context i j).outcome = expected


def officialComparisonTheoremExport
    (mExpr contextExpr leftExpr rightExpr expectedExpr theoremName proofTerm : String) :
    LeanTheoremExport where
  imports := ["TetraStereo.OneCenter.CertificateExport"]
  theoremName := theoremName
  statement :=
    "(" ++ mExpr ++ ".cipOfficialCompare " ++ contextExpr ++ " " ++ leftExpr ++ " " ++
      rightExpr ++ ").outcome = " ++ expectedExpr
  proofTerm := proofTerm

/-- Compile a checked official one-center ligand comparison into a theorem artifact. -/
def compileOfficialComparisonCertificate {V : Type*} [Fintype V] [DecidableEq V]
    (theoremName mExpr contextExpr leftExpr rightExpr expectedExpr proofTerm : String)
    (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (i j : Fin 4) (expected : Ordering)
    (h : OfficialComparisonCertificateClaim m context i j expected) :
    LeanCertificateArtifact where
  kind := LeanCertificateKind.officialLigandComparison
  title := "Official CIP ligand comparison"
  theoremExport :=
    officialComparisonTheoremExport mExpr contextExpr leftExpr rightExpr expectedExpr theoremName
      proofTerm
  claim := OfficialComparisonCertificateClaim m context i j expected
  proof := h

/-- Claim that a safe optional `R/S` computation returns the expected descriptor. -/
def RSAssignmentCertificateClaim (computed : Option RS) (expected : RS) : Prop :=
  computed = some expected


def rsAssignmentTheoremExport (computedExpr expectedExpr theoremName proofTerm : String) :
    LeanTheoremExport where
  imports := ["TetraStereo.OneCenter.CertificateExport"]
  theoremName := theoremName
  statement :=
    "TetraStereo.OneCenter.RSAssignmentCertificateClaim " ++ computedExpr ++ " " ++
      expectedExpr
  proofTerm := proofTerm

/-- Compile a checked safe `R/S` assignment into a theorem artifact. -/
def compileRSAssignmentCertificate (theoremName computedExpr expectedExpr proofTerm : String)
    (computed : Option RS) (expected : RS)
    (h : RSAssignmentCertificateClaim computed expected) :
    LeanCertificateArtifact where
  kind := LeanCertificateKind.rsAssignment
  title := "Safe R/S assignment"
  theoremExport := rsAssignmentTheoremExport computedExpr expectedExpr theoremName proofTerm
  claim := RSAssignmentCertificateClaim computed expected
  proof := h

/-- Claim that a safe optional `R/S` computation refused to assign a descriptor. -/
def RSRefusalCertificateClaim (computed : Option RS) : Prop :=
  computed = none


def rsRefusalTheoremExport (computedExpr theoremName proofTerm : String) :
    LeanTheoremExport where
  imports := ["TetraStereo.OneCenter.CertificateExport"]
  theoremName := theoremName
  statement := "TetraStereo.OneCenter.RSRefusalCertificateClaim " ++ computedExpr
  proofTerm := proofTerm

/-- Compile a checked safe `R/S` refusal into a theorem artifact. -/
def compileRSRefusalCertificate (theoremName computedExpr proofTerm : String)
    (computed : Option RS) (h : RSRefusalCertificateClaim computed) :
    LeanCertificateArtifact where
  kind := LeanCertificateKind.rsRefusal
  title := "Safe R/S refusal"
  theoremExport := rsRefusalTheoremExport computedExpr theoremName proofTerm
  claim := RSRefusalCertificateClaim computed
  proof := h

end
end OneCenter
end TetraStereo
