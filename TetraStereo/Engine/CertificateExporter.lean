import TetraStereo.OneCenter.CertificateExport

set_option autoImplicit false

namespace TetraStereo
namespace Engine

open OneCenter









/-- A named certificate that a host exporter can write as a generated Lean theorem file. -/
structure CertificateSourceEntry where
  key : String
  description : String
  fileName : String
  source : String

namespace CertificateSourceEntry

/-- Rendered Lean theorem source for this export entry, with a final newline for files. -/
def fileSource (entry : CertificateSourceEntry) : String :=
  entry.source ++ "\n"

/-- The generated file path for this entry under an output directory. -/
def outputPath (entry : CertificateSourceEntry) (outputDirectory : String) : System.FilePath :=
  System.FilePath.mk (outputDirectory ++ "/" ++ entry.fileName)

/-- Write this entry's rendered Lean theorem source into an output directory. -/
def writeSource (entry : CertificateSourceEntry) (outputDirectory : String) :
    IO System.FilePath := do
  IO.FS.createDirAll (System.FilePath.mk outputDirectory)
  let path := entry.outputPath outputDirectory
  IO.FS.writeFile path entry.fileSource
  pure path

end CertificateSourceEntry

/-- Write Lean source to an exact file path, creating parent directories first. -/
def writeLeanSourceFile (path : System.FilePath) (source : String) : IO System.FilePath := do
  match path.parent with
  | some parent => IO.FS.createDirAll parent
  | none => pure ()
  IO.FS.writeFile path (source ++ "\n")
  pure path

/-- A named checked artifact paired with its host-export metadata. -/
structure CertificateExportEntry extends CertificateSourceEntry where
  artifact : LeanCertificateArtifact

namespace CertificateExportEntry

/-- The executable source-entry view of a checked artifact entry. -/
def toSourceEntry (entry : CertificateExportEntry) : CertificateSourceEntry :=
  { key := entry.key
    description := entry.description
    fileName := entry.fileName
    source := entry.artifact.source }

end CertificateExportEntry

/-- Result of checking a generated Lean certificate file through the external Lean verifier. -/
structure CertificateVerificationResult where
  path : System.FilePath
  exitCode : UInt32
  stdout : String
  stderr : String

namespace CertificateVerificationResult

/-- Whether the verifier accepted the generated certificate file. -/
def passed (result : CertificateVerificationResult) : Bool :=
  result.exitCode == 0

end CertificateVerificationResult

/-- Path-list separator used by Lean's `LEAN_PATH` on the current supported host platform. -/
def leanPathListSeparator : String := ":"

/-- Whether a path is unsafe to embed directly as one entry in `LEAN_PATH`. -/
def leanPathEntryHasSeparator (path : String) : Bool :=
  path.toList.contains ':'

/-- Run `lake env lean` on a generated certificate file. -/
def verifyLeanCertificateFile (path : System.FilePath) : IO CertificateVerificationResult := do
  let output ← IO.Process.output
    { cmd := "lake"
      args := #["env", "lean", path.toString] }
  pure
    { path := path
      exitCode := output.exitCode
      stdout := output.stdout
      stderr := output.stderr }

/-- Run Lean on a generated Lean file with extra roots prepended to `LEAN_PATH`.

This is used for generated packages where one generated certificate imports another generated
module that has just been compiled into a private generated-olean root.  Suite manifests also use
this to expose both generated source roots and generated `.olean` roots at once. -/
def verifyLeanCertificateFileWithRootAndLeanPathRoots
    (sourceRoot : String) (leanPathRoots : List String) (path : System.FilePath) :
    IO CertificateVerificationResult := do
  let roots := leanPathRoots.filter fun root => root ≠ ""
  match roots.find? leanPathEntryHasSeparator with
  | some root =>
    pure
      { path := path
        exitCode := 1
        stdout := ""
        stderr := "generated Lean path root contains the LEAN_PATH separator: " ++ root }
  | none =>
      let lakeLeanPathOutput ← IO.Process.output
        { cmd := "lake"
          args := #["env", "printenv", "LEAN_PATH"] }
      if lakeLeanPathOutput.exitCode != 0 then
        pure
          { path := path
            exitCode := lakeLeanPathOutput.exitCode
            stdout := lakeLeanPathOutput.stdout
            stderr := lakeLeanPathOutput.stderr }
      else
      let baseLeanPath := lakeLeanPathOutput.stdout.trimAscii.toString
      let allRoots :=
        if baseLeanPath = "" then roots
        else roots ++ [baseLeanPath]
      let leanPath :=
        String.intercalate leanPathListSeparator allRoots
      let output ← IO.Process.output
        { cmd := "lake"
          args := #["env", "lean", "-R", sourceRoot, path.toString]
          env := #[("LEAN_PATH", some leanPath)] }
      pure
        { path := path
          exitCode := output.exitCode
          stdout := output.stdout
          stderr := output.stderr }

/-- Run Lean on a generated Lean file with one extra root prepended to `LEAN_PATH`. -/
def verifyLeanCertificateFileWithRootAndLeanPath
    (sourceRoot leanPathRoot : String) (path : System.FilePath) :
    IO CertificateVerificationResult :=
  verifyLeanCertificateFileWithRootAndLeanPathRoots sourceRoot [leanPathRoot] path

/-- Run Lean on a generated Lean file with the same root used for module naming and imports. -/
def verifyLeanCertificateFileWithLeanPathRoot
    (leanPathRoot : String) (path : System.FilePath) : IO CertificateVerificationResult :=
  verifyLeanCertificateFileWithRootAndLeanPath leanPathRoot leanPathRoot path

/-- Compile a generated Lean module to an `.olean` with extra roots prepended to `LEAN_PATH`. -/
def compileLeanModuleFileWithRootAndLeanPathRoots
    (sourceRoot : String) (leanPathRoots : List String)
    (path oleanPath : System.FilePath) :
    IO CertificateVerificationResult := do
  match oleanPath.parent with
  | some parent => IO.FS.createDirAll parent
  | none => pure ()
  let roots := leanPathRoots.filter fun root => root ≠ ""
  match roots.find? leanPathEntryHasSeparator with
  | some root =>
      pure
        { path := path
          exitCode := 1
          stdout := ""
          stderr := "generated Lean path root contains the LEAN_PATH separator: " ++ root }
  | none =>
      let lakeLeanPathOutput ← IO.Process.output
        { cmd := "lake"
          args := #["env", "printenv", "LEAN_PATH"] }
      if lakeLeanPathOutput.exitCode != 0 then
        pure
          { path := path
            exitCode := lakeLeanPathOutput.exitCode
            stdout := lakeLeanPathOutput.stdout
            stderr := lakeLeanPathOutput.stderr }
      else
      let baseLeanPath := lakeLeanPathOutput.stdout.trimAscii.toString
      let allRoots :=
        if baseLeanPath = "" then roots
        else roots ++ [baseLeanPath]
      let leanPath :=
        String.intercalate leanPathListSeparator allRoots
      let output ← IO.Process.output
        { cmd := "lake"
          args := #["env", "lean", "-R", sourceRoot, "-o", oleanPath.toString, path.toString]
          env := #[("LEAN_PATH", some leanPath)] }
      pure
        { path := path
          exitCode := output.exitCode
          stdout := output.stdout
          stderr := output.stderr }

/-- Compile a generated Lean module to an `.olean` under a package root. -/
def compileLeanModuleFileWithRoot
    (packageRoot : String) (path oleanPath : System.FilePath) :
    IO CertificateVerificationResult :=
  compileLeanModuleFileWithRootAndLeanPathRoots packageRoot [] path oleanPath

/-- Write one certificate source entry and immediately verify the generated file. -/
def writeAndVerifyCertificate (entry : CertificateSourceEntry) (outputDirectory : String) :
    IO CertificateVerificationResult := do
  let path ← entry.writeSource outputDirectory
  verifyLeanCertificateFile path

/-- Find a named certificate source entry by host-facing key. -/
def findCertificateEntry? (entries : List CertificateSourceEntry) (key : String) :
    Option CertificateSourceEntry :=
  entries.find? fun entry => entry.key == key

end Engine
end TetraStereo
