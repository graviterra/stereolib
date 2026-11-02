import TetraStereo.Engine.CertificateExporter
import TetraStereo.Examples.CertificateExport
import TetraStereo.Examples.EngineClaims
import TetraStereo.Examples.EngineRefusal
import TetraStereo.Examples.EngineTransaction
import TetraStereo.Examples.OfficialStereoBuilder
import TetraStereo.Examples.OfficialStereoTransaction
import TetraStereo.Examples.PublicAPI

set_option autoImplicit false

namespace TetraStereo
namespace Examples
namespace CertificateExportRegistry

open OneCenter

noncomputable section

/-- Build a checked export entry and keep its executable source aligned with the artifact. -/
def checkedEntry (key description fileName : String) (artifact : LeanCertificateArtifact) :
    Engine.CertificateExportEntry where
  key := key
  description := description
  fileName := fileName
  source := artifact.source
  artifact := artifact

/-- Export entry for the preserved original `C(F)(O)(N)Cl` example.

The registered artifact is the checked wrapper around the actual builder's prepared transaction:
its claim/proof are the builder's own, and its rendered source is a standalone theorem for that
claim (never the retired refusal text). -/
def autoBridgeCheckedEntry : Engine.CertificateExportEntry :=
  checkedEntry
    "auto-bridge-official-stereo-checked"
    "checked auto-built official-stereo prepared transaction from checked intake"
    "AutoBridgeOfficialStereoChecked.lean"
    OfficialStereoBuilder.autoBridgeCheckedArtifact

/-- Public demo certificates that can be exported as standalone generated Lean files. -/
def publicDemoCertificates : List Engine.CertificateExportEntry :=
  [ checkedEntry
      "import-methane"
      "checked raw methane import-normalization certificate"
      "MethaneImportCertificate.lean"
      CertificateExport.methaneImportArtifact
  , checkedEntry
      "trace-1-phenylethanol-phenyl-vs-methyl"
      "checked CIP trace outcome for 1-phenylethanol phenyl vs methyl"
      "OnePhenylethanolPhenylMethylTrace.lean"
      CertificateExport.onePhenylethanolMethylPhenylArtifact
  , checkedEntry
      "rs-1-phenylethanol-right"
      "checked safe public S assignment for right-handed 1-phenylethanol"
      "OnePhenylethanolRightRS.lean"
      CertificateExport.onePhenylethanolRightRSArtifact
  , checkedEntry
      "engine-1-phenylethanol-right"
      "checked public engine transaction for right-handed 1-phenylethanol"
      "OnePhenylethanolEngineRightRS.lean"
      EngineTransaction.onePhenylethanolEngineCertified.artifact
  , checkedEntry
      "engine-methane-refusal"
      "checked public engine refusal for methane tied priorities"
      "MethaneEngineRefusal.lean"
      EngineRefusal.methaneEngineCertifiedRefusal.artifact
  , checkedEntry
      "claim-official-cip"
      "checked broad public official-CIP claim transaction"
      "OfficialCIPClaim.lean"
      EngineClaims.officialCIPClaimCertificate.artifact
  , checkedEntry
      "claim-multicenter-relation"
      "checked broad public multi-center relation claim transaction"
      "MultiCenterRelationClaim.lean"
      EngineClaims.multiCenterRelationClaimCertificate.artifact
  , checkedEntry
      "claim-ensemble"
      "checked broad public ensemble stereochemistry claim transaction"
      "EnsembleClaim.lean"
      EngineClaims.ensembleClaimCertificate.artifact
  , checkedEntry
      "official-stereo-helical"
      "checked detector-backed helical M/P official-stereo transaction"
      "OfficialStereoHelical.lean"
      OfficialStereoTransaction.helicalBranchCertificate.artifact
  , checkedEntry
      "official-stereo-graph-key"
      "checked detector-free oxygen-before-carbon graph-key transaction"
      "OfficialStereoGraphKey.lean"
      OfficialStereoTransaction.graphKeyCertificate.artifact
  , checkedEntry
      "official-stereo-default-fuel"
      "checked default-fuel official graph-key transaction"
      "OfficialStereoDefaultFuel.lean"
      OfficialStereoTransaction.graphKeyDefaultFuelCertificate.artifact
  , checkedEntry
      "official-stereo-multiple-bond"
      "checked multiple-bond duplicate-node official-stereo transaction"
      "OfficialStereoMultipleBond.lean"
      OfficialStereoTransaction.multipleBondCertificate.artifact
  , checkedEntry
      "official-stereo-virtual-auxiliary"
      "checked virtual auxiliary-node official-stereo transaction"
      "OfficialStereoVirtualAuxiliary.lean"
      OfficialStereoTransaction.virtualAuxiliaryCertificate.artifact
  , checkedEntry
      "official-stereo-empty-refusal"
      "checked official-stereo refusal for unresolved detector/graph priorities"
      "OfficialStereoEmptyRefusal.lean"
      OfficialStereoTransaction.emptyDetectorRefusal.artifact
  , autoBridgeCheckedEntry
  , checkedEntry
      "ccl4-official-stereo-refusal"
      "checked actual CCl4 automatic-builder refusal from checked intake"
      "CCl4OfficialStereoRefusal.lean"
      OfficialStereoBuilder.ccl4Refusal.artifact
  ]

/-- Number of exportable public demo certificates in the registry. -/
theorem publicDemoCertificates_length :
    publicDemoCertificates.length = 16 :=
  rfl

/-- The preserved original example's registry key is the checked key. -/
theorem autoBridgeCheckedEntry_key :
    autoBridgeCheckedEntry.key = "auto-bridge-official-stereo-checked" :=
  rfl

/-- The preserved original example's generated file name is the checked file name. -/
theorem autoBridgeCheckedEntry_fileName :
    autoBridgeCheckedEntry.fileName = "AutoBridgeOfficialStereoChecked.lean" :=
  rfl

/-- The preserved original example's emitted source is the standalone checked wrapper source. -/
theorem autoBridgeCheckedEntry_source :
    autoBridgeCheckedEntry.source =
      OfficialStereoBuilder.autoBridgeCheckedTheoremExport.source :=
  rfl

/-- The preserved original example's registered artifact carries the builder's checked claim. -/
theorem autoBridgeCheckedEntry_claim :
    autoBridgeCheckedEntry.artifact.claim :=
  OfficialStereoBuilder.autoBridgeCheckedArtifact_claim

/-- Every registry entry carries a checked theorem artifact before any file is written. -/
theorem publicDemoCertificates_checked :
    ∀ entry, entry ∈ publicDemoCertificates → entry.artifact.claim := by
  intro entry _hmem
  exact entry.artifact.proof

end
end CertificateExportRegistry
end Examples
end TetraStereo
