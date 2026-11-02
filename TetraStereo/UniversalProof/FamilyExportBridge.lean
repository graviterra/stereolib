import TetraStereo.Engine.Claims
import TetraStereo.Engine.CertificateExporter

set_option autoImplicit false

namespace TetraStereo.UniversalProof.FamilyExportBridge

open TetraStereo.OneCenter TetraStereo.Engine

/-! A common export adapter. It packages an already proved proposition; it does not
establish scientific meaning or replace independent verification of emitted source. -/

structure Metadata where
  key : String
  description : String
  fileName : String

def sourceEntry (metadata : Metadata) (artifact : LeanCertificateArtifact) : CertificateSourceEntry where
  key := metadata.key
  description := metadata.description
  fileName := metadata.fileName
  source := artifact.source

theorem sourceEntry_source (metadata : Metadata) (artifact : LeanCertificateArtifact) :
    (sourceEntry metadata artifact).source = artifact.source := rfl

def write (entry : CertificateSourceEntry) (outputDirectory : String) : IO System.FilePath :=
  entry.writeSource outputDirectory

theorem write_emits_renderer (entry : CertificateSourceEntry) (outputDirectory : String) :
    write entry outputDirectory = (do
      IO.FS.createDirAll (System.FilePath.mk outputDirectory)
      let path := entry.outputPath outputDirectory
      IO.FS.writeFile path entry.fileSource
      pure path) := rfl

theorem inhabited_artifact (metadata : Metadata) (artifact : LeanCertificateArtifact)
    (claim : Prop) (sameClaim : artifact.claim = claim) :
    ∃ checked : LeanCertificateArtifact, checked = artifact ∧ checked.claim = claim ∧
      checked.claim ∧ checked.source = (sourceEntry metadata artifact).source :=
  ⟨artifact, rfl, sameClaim, artifact.checked, rfl⟩

end TetraStereo.UniversalProof.FamilyExportBridge
