import TetraStereo.OneCenter.CertificateExport
import TetraStereo.Examples.OnePhenylethanol

set_option autoImplicit false

namespace TetraStereo
namespace Examples
namespace CertificateExport

open OneCenter

noncomputable section

/-!
  Smoke tests for the certificate-export boundary.

  These are not external files yet.  They are checked Lean values showing the path a host exporter
  will use: bridge molecule or engine result in, theorem artifact with a checked claim out.

  The `R/S` artifacts use the corrected negative-orientation calibration
  (`RS.ofHandedness (-1) = RS.R`): the canonical right-hand 1-phenylethanol realization is `S`, and
  the left-hand realization is `R`.  The pair is exported together so the disagreement of the two
  realizations is itself part of the checked export batch.
-/

def methaneRaw : RawMolecule where
  atoms := [AtomSpec.aliphatic Element.C]
  bonds := []

def methanePacket : ExternalRawMoleculePacket :=
  rawMoleculePacket methaneRaw ChemistryImportTrust.proofCertifiedAdapter

def methaneImportArtifact : LeanCertificateArtifact :=
  compileRawImportCertificate methanePacket "methanePacket" "methane_import_normalizes"

theorem methaneImportArtifact_checked :
    methaneImportArtifact.claim :=
  methaneImportArtifact.checked

/-- Imports needed by generated theorem text that mentions the 1-phenylethanol example. -/
def onePhenylethanolExportImports : List String :=
  ["TetraStereo.OneCenter.CertificateExport", "TetraStereo.Examples.OnePhenylethanol"]

def onePhenylethanolMethylPhenylArtifact : LeanCertificateArtifact :=
  let base :=
    compileTraceOutcomeCertificate
      "one_phenylethanol_methyl_phenyl_trace"
      "(TetraStereo.Examples.OnePhenylethanol.oneCenter.cipDescriptorEngine.compare (2 : Fin 4) (1 : Fin 4))"
      "Ordering.lt"
      "  exact TetraStereo.Examples.OnePhenylethanol.cipDescriptorEngine_methyl_phenyl_outcome"
      (OnePhenylethanol.oneCenter.cipDescriptorEngine.compare (2 : Fin 4) (1 : Fin 4))
      Ordering.lt
      OnePhenylethanol.cipDescriptorEngine_methyl_phenyl_outcome
  { base with
    theoremExport :=
      { base.theoremExport with
        imports := onePhenylethanolExportImports
        namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"] } }

theorem onePhenylethanolMethylPhenylArtifact_checked :
    onePhenylethanolMethylPhenylArtifact.claim :=
  onePhenylethanolMethylPhenylArtifact.checked

/-- Checked export of the right-hand 1-phenylethanol safe descriptor, namely `S`. -/
def onePhenylethanolRightRSArtifact : LeanCertificateArtifact :=
  let base :=
    compileRSAssignmentCertificate
      "one_phenylethanol_right_rs"
      "(TetraStereo.Examples.OnePhenylethanol.oneCenter.rsCIP? TetraStereo.Examples.OnePhenylethanol.rightRealization)"
      "TetraStereo.OneCenter.RS.S"
      "  exact TetraStereo.Examples.OnePhenylethanol.rsCIP?_right_eq_some_S"
      (OnePhenylethanol.oneCenter.rsCIP? OnePhenylethanol.rightRealization)
      RS.S
      OnePhenylethanol.rsCIP?_right_eq_some_S
  { base with
    theoremExport :=
      { base.theoremExport with
        imports := onePhenylethanolExportImports
        namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"] } }

theorem onePhenylethanolRightRSArtifact_checked :
    onePhenylethanolRightRSArtifact.claim :=
  onePhenylethanolRightRSArtifact.checked

/-- Checked export of the left-hand 1-phenylethanol safe descriptor, namely `R`. -/
def onePhenylethanolLeftRSArtifact : LeanCertificateArtifact :=
  let base :=
    compileRSAssignmentCertificate
      "one_phenylethanol_left_rs"
      "(TetraStereo.Examples.OnePhenylethanol.oneCenter.rsCIP? TetraStereo.Examples.OnePhenylethanol.leftRealization)"
      "TetraStereo.OneCenter.RS.R"
      "  exact TetraStereo.Examples.OnePhenylethanol.rsCIP?_left_eq_some_R"
      (OnePhenylethanol.oneCenter.rsCIP? OnePhenylethanol.leftRealization)
      RS.R
      OnePhenylethanol.rsCIP?_left_eq_some_R
  { base with
    theoremExport :=
      { base.theoremExport with
        imports := onePhenylethanolExportImports
        namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"] } }

theorem onePhenylethanolLeftRSArtifact_checked :
    onePhenylethanolLeftRSArtifact.claim :=
  onePhenylethanolLeftRSArtifact.checked

def exampleCertificateBatch : LeanCertificateBatch where
  artifacts :=
    [ methaneImportArtifact
    , onePhenylethanolMethylPhenylArtifact
    , onePhenylethanolRightRSArtifact
    , onePhenylethanolLeftRSArtifact
    ]

theorem exampleCertificateBatch_checked :
    exampleCertificateBatch.AllClaims :=
  exampleCertificateBatch.checked

example :
    methaneImportArtifact.kind = LeanCertificateKind.importNormalization :=
  rfl

example :
    onePhenylethanolMethylPhenylArtifact.kind = LeanCertificateKind.traceOutcome :=
  rfl

example :
    onePhenylethanolRightRSArtifact.kind = LeanCertificateKind.rsAssignment :=
  rfl

example :
    onePhenylethanolLeftRSArtifact.kind = LeanCertificateKind.rsAssignment :=
  rfl

end
end CertificateExport
end Examples
end TetraStereo
