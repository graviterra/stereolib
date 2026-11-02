import TetraStereo.CLI.CertificateSourceRegistry
import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false

namespace TetraStereo
namespace CLI

open Engine
open CertificateSourceRegistry

/-- Short command-line usage text for the certificate exporter. -/
def usage : String :=
  "usage:\n" ++
  "  lake exe tetrastereo_cert assign <smiles>\n" ++
  "  lake exe tetrastereo_cert assign-file <path>\n" ++
  "  lake exe tetrastereo_cert list\n" ++
  "  lake exe tetrastereo_cert source <key>\n" ++
  "  lake exe tetrastereo_cert write <key> <output-dir>\n" ++
  "  lake exe tetrastereo_cert write-all <output-dir>\n" ++
  "  lake exe tetrastereo_cert verify <key> <output-dir>\n" ++
  "  lake exe tetrastereo_cert verify-all <output-dir>\n" ++
  "  lake exe tetrastereo_cert host-list\n" ++
  "  lake exe tetrastereo_cert host-source <key>\n" ++
  "  lake exe tetrastereo_cert host-write <key> <output-dir>\n" ++
  "  lake exe tetrastereo_cert host-verify <key> <output-dir>\n" ++
  "  lake exe tetrastereo_cert host-package-list\n" ++
  "  lake exe tetrastereo_cert host-package-write <key> <output-dir>\n" ++
  "  lake exe tetrastereo_cert host-package-verify <key> <output-dir>\n" ++
  "  lake exe tetrastereo_cert host-claim-list\n" ++
  "  lake exe tetrastereo_cert host-claim-source <key>\n" ++
  "  lake exe tetrastereo_cert host-claim-write <key> <output-dir>\n" ++
  "  lake exe tetrastereo_cert host-claim-verify <key> <output-dir>\n" ++
  "  lake exe tetrastereo_cert host-claim-verify-all <output-dir>\n" ++
  "  lake exe tetrastereo_cert host-suite-list\n" ++
  "  lake exe tetrastereo_cert host-suite-write <key> <output-dir>\n" ++
  "  lake exe tetrastereo_cert host-suite-verify <key> <output-dir>\n" ++
  "  lake exe tetrastereo_cert host-analysis-list\n" ++
  "  lake exe tetrastereo_cert host-analysis-write <key> <output-dir>\n" ++
  "  lake exe tetrastereo_cert host-analysis-verify <key> <output-dir>"

/-- Print one registry line. -/
def printEntryLine (entry : CertificateSourceEntry) : IO Unit :=
  IO.println (entry.key ++ "\t" ++ entry.description)

/-- Print all known certificate keys. -/
def printCertificateList : IO Unit := do
  for entry in publicDemoCertificateSources do
    printEntryLine entry

/-- Print all known generated-host-module keys. -/
def printHostModuleList : IO Unit := do
  for entry in publicDemoHostModuleSources do
    printEntryLine entry

/-- Print all known two-stage host certificate package keys. -/
def printHostPackageList : IO Unit := do
  for request in publicDemoHostRequests do
    IO.println (request.key ++ "\t" ++ request.description)

/-- Print all known broad host claim package keys. -/
def printHostClaimList : IO Unit := do
  for request in publicDemoHostClaimRequests do
    IO.println (request.key ++ "\t" ++ request.description)

/-- Print all known host analysis-suite package keys. -/
def printHostAnalysisSuiteList : IO Unit := do
  for request in publicDemoHostAnalysisSuites do
    IO.println (request.key ++ "\t" ++ request.description)

/-- Print all known molecule-analysis request keys. -/
def printHostMoleculeAnalysisList : IO Unit := do
  for request in publicDemoHostMoleculeAnalysisRequests do
    IO.println (request.key ++ "\t" ++ request.description)

/-- Whether a process stream has non-whitespace text worth printing. -/
def hasOutputText (text : String) : Bool :=
  text.trimAscii.toString ≠ ""

/-- Find a registry entry or print an actionable error. -/
def requireEntry (key : String) : IO (Option CertificateSourceEntry) := do
  match findCertificateEntry? publicDemoCertificateSources key with
  | some entry => pure (some entry)
  | none =>
      IO.eprintln ("unknown certificate key: " ++ key)
      IO.eprintln "run `lake exe tetrastereo_cert list` to see available keys"
      pure none

/-- Find a generated host-module entry or print an actionable error. -/
def requireHostModuleEntry (key : String) : IO (Option CertificateSourceEntry) := do
  match findCertificateEntry? publicDemoHostModuleSources key with
  | some entry => pure (some entry)
  | none =>
      IO.eprintln ("unknown host module key: " ++ key)
      IO.eprintln "run `lake exe tetrastereo_cert host-list` to see available keys"
      pure none

/-- Find a structured host request or print an actionable error. -/
def requireHostRequest (key : String) : IO (Option HostOfficialStereoRequest) := do
  match findHostRequest? key with
  | some request => pure (some request)
  | none =>
      IO.eprintln ("unknown host package key: " ++ key)
      IO.eprintln "run `lake exe tetrastereo_cert host-package-list` to see available keys"
      pure none

/-- Find a broad host claim request or print an actionable error. -/
def requireHostClaimRequest (key : String) : IO (Option HostStereoClaimRequest) := do
  match findHostClaimRequest? key with
  | some request => pure (some request)
  | none =>
      IO.eprintln ("unknown host claim key: " ++ key)
      IO.eprintln "run `lake exe tetrastereo_cert host-claim-list` to see available keys"
      pure none

/-- Find a host analysis-suite request or print an actionable error. -/
def requireHostAnalysisSuiteRequest (key : String) :
    IO (Option HostAnalysisSuiteRequest) := do
  match findHostAnalysisSuite? key with
  | some request => pure (some request)
  | none =>
      IO.eprintln ("unknown host suite key: " ++ key)
      IO.eprintln "run `lake exe tetrastereo_cert host-suite-list` to see available keys"
      pure none

/-- Find a host molecule-analysis request or print an actionable error. -/
def requireHostMoleculeAnalysisRequest (key : String) :
    IO (Option HostMoleculeAnalysisRequest) := do
  match findHostMoleculeAnalysisRequest? key with
  | some request => pure (some request)
  | none =>
      IO.eprintln ("unknown host molecule analysis key: " ++ key)
      IO.eprintln "run `lake exe tetrastereo_cert host-analysis-list` to see available keys"
      pure none

/-- Write one entry and report the generated path. -/
def writeOne (entry : CertificateSourceEntry) (outputDirectory : String) : IO UInt32 := do
  let path ← entry.writeSource outputDirectory
  IO.println ("wrote " ++ path.toString)
  pure 0

/-- Write all registry entries and report their generated paths. -/
def writeAll (outputDirectory : String) : IO UInt32 := do
  for entry in publicDemoCertificateSources do
    let path ← entry.writeSource outputDirectory
    IO.println ("wrote " ++ path.toString)
  pure 0

/-- Print verifier output and return the verifier exit code. -/
def reportVerification (result : CertificateVerificationResult) : IO UInt32 := do
  if result.passed then
    IO.println ("verified " ++ result.path.toString)
  else
    IO.eprintln ("verification failed for " ++ result.path.toString)
    if hasOutputText result.stdout then
      IO.eprintln result.stdout
    if hasOutputText result.stderr then
      IO.eprintln result.stderr
  pure result.exitCode

/-- Print a named package-verification step and return the verifier/compiler exit code. -/
def reportPackageStep (verb : String) (result : CertificateVerificationResult) : IO UInt32 := do
  if result.passed then
    IO.println (verb ++ " " ++ result.path.toString)
  else
    IO.eprintln (verb ++ " failed for " ++ result.path.toString)
    if hasOutputText result.stdout then
      IO.eprintln result.stdout
    if hasOutputText result.stderr then
      IO.eprintln result.stderr
  pure result.exitCode

/-- Write and verify one registry entry. -/
def verifyOne (entry : CertificateSourceEntry) (outputDirectory : String) : IO UInt32 := do
  let result ← writeAndVerifyCertificate entry outputDirectory
  reportVerification result

/-- Write and verify all registry entries. -/
def verifyAll (outputDirectory : String) : IO UInt32 := do
  let mut failed := false
  for entry in publicDemoCertificateSources do
    let result ← writeAndVerifyCertificate entry outputDirectory
    if result.passed then
      IO.println ("verified " ++ result.path.toString)
    else
      failed := true
      IO.eprintln ("verification failed for " ++ result.path.toString)
      if hasOutputText result.stdout then
        IO.eprintln result.stdout
      if hasOutputText result.stderr then
        IO.eprintln result.stderr
  pure (if failed then 1 else 0)

/-- Write a two-stage generated host package: host module plus downstream certificate theorem. -/
def writeHostPackage (request : HostOfficialStereoRequest) (outputDirectory : String) :
    IO UInt32 := do
  let paths ← request.writePackageSources outputDirectory
  IO.println ("wrote " ++ paths.hostModulePath.toString)
  IO.println ("wrote " ++ paths.certificatePath.toString)
  pure 0

/-- Write and verify a two-stage generated host package. -/
def verifyHostPackage (request : HostOfficialStereoRequest) (outputDirectory : String) :
    IO UInt32 := do
  let paths ← request.writePackageSources outputDirectory
  let hostResult ← compileLeanModuleFileWithRoot outputDirectory
    paths.hostModulePath paths.hostModuleOLeanPath
  let hostExit ← reportPackageStep "compiled host module" hostResult
  if hostExit == 0 then
    let certificateResult ← verifyLeanCertificateFileWithRootAndLeanPath outputDirectory
      (request.packageOLeanRoot outputDirectory) paths.certificatePath
    reportPackageStep "verified certificate" certificateResult
  else
    pure hostExit

/-- Write a generated broad host claim theorem package. -/
def writeHostClaimPackage (request : HostStereoClaimRequest) (outputDirectory : String) :
    IO UInt32 := do
  let path ← request.writePackageSource outputDirectory
  IO.println ("wrote " ++ path.toString)
  pure 0

/-- Write and verify a generated broad host claim theorem package. -/
def verifyHostClaimPackage (request : HostStereoClaimRequest) (outputDirectory : String) :
    IO UInt32 := do
  let result ← request.writeAndVerifyPackageSource outputDirectory
  reportVerification result

/-- Write and verify every generated broad host claim theorem package. -/
def verifyAllHostClaimPackages (outputDirectory : String) : IO UInt32 := do
  let mut failed := false
  for request in publicDemoHostClaimRequests do
    let result ← request.writeAndVerifyPackageSource outputDirectory
    if result.passed then
      IO.println ("verified " ++ result.path.toString)
    else
      failed := true
      IO.eprintln ("verification failed for " ++ result.path.toString)
      if hasOutputText result.stdout then
        IO.eprintln result.stdout
      if hasOutputText result.stderr then
        IO.eprintln result.stderr
  pure (if failed then 1 else 0)

/-- Write a generated host analysis suite package. -/
def writeHostAnalysisSuitePackage
    (request : HostAnalysisSuiteRequest) (outputDirectory : String) : IO UInt32 := do
  let paths ← request.writePackageSources outputDirectory
  for packagePaths in paths.officialPackagePaths do
    IO.println ("wrote " ++ packagePaths.hostModulePath.toString)
    IO.println ("wrote " ++ packagePaths.certificatePath.toString)
  for path in paths.claimPaths do
    IO.println ("wrote " ++ path.toString)
  for path in paths.witnessPaths do
    IO.println ("wrote " ++ path.toString)
  IO.println ("wrote " ++ paths.manifestPath.toString)
  pure 0

/-- Report all steps in a generated host analysis-suite verification. -/
def reportHostAnalysisSuiteVerification
    (result : HostAnalysisSuiteRequest.VerificationResult) : IO UInt32 := do
  for stepResult in result.officialHostModuleResults do
    let _ ← reportPackageStep "compiled suite host module" stepResult
  for stepResult in result.officialCertificateCompileResults do
    let _ ← reportPackageStep "compiled suite official certificate" stepResult
  for stepResult in result.claimCompileResults do
    let _ ← reportPackageStep "compiled suite broad claim" stepResult
  for stepResult in result.witnessCompileResults do
    let _ ← reportPackageStep "compiled suite target certificate package" stepResult
  let _ ← reportPackageStep "verified suite manifest" result.manifestResult
  pure (if result.passed then 0 else 1)

/-- Write and verify a generated host analysis suite package. -/
def verifyHostAnalysisSuitePackage
    (request : HostAnalysisSuiteRequest) (outputDirectory : String) : IO UInt32 := do
  let result ← request.writeAndVerifyPackageSources outputDirectory
  reportHostAnalysisSuiteVerification result

/-- Write the generated suite induced by a molecule-analysis request. -/
def writeHostMoleculeAnalysisPackage
    (request : HostMoleculeAnalysisRequest) (outputDirectory : String) : IO UInt32 := do
  let paths ← request.writeSuitePackageSources outputDirectory
  for packagePaths in paths.officialPackagePaths do
    IO.println ("wrote " ++ packagePaths.hostModulePath.toString)
    IO.println ("wrote " ++ packagePaths.certificatePath.toString)
  for path in paths.claimPaths do
    IO.println ("wrote " ++ path.toString)
  for path in paths.witnessPaths do
    IO.println ("wrote " ++ path.toString)
  IO.println ("wrote " ++ paths.manifestPath.toString)
  pure 0

/-- Write and verify the generated suite induced by a molecule-analysis request. -/
def verifyHostMoleculeAnalysisPackage
    (request : HostMoleculeAnalysisRequest) (outputDirectory : String) : IO UInt32 := do
  let result ← request.writeAndVerifySuitePackageSources outputDirectory
  reportHostAnalysisSuiteVerification result

/-- Command-line entry point for writing and verifying generated certificate files. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["list"] =>
      printCertificateList
      pure 0
  | ["source", key] =>
      match ← requireEntry key with
      | some entry =>
          IO.println entry.source
          pure 0
      | none => pure 2
  | ["write", key, outputDirectory] =>
      match ← requireEntry key with
      | some entry => writeOne entry outputDirectory
      | none => pure 2
  | ["write-all", outputDirectory] =>
      writeAll outputDirectory
  | ["verify", key, outputDirectory] =>
      match ← requireEntry key with
      | some entry => verifyOne entry outputDirectory
      | none => pure 2
  | ["verify-all", outputDirectory] =>
      verifyAll outputDirectory
  | ["host-list"] =>
      printHostModuleList
      pure 0
  | ["host-source", key] =>
      match ← requireHostModuleEntry key with
      | some entry =>
          IO.println entry.source
          pure 0
      | none => pure 2
  | ["host-write", key, outputDirectory] =>
      match ← requireHostModuleEntry key with
      | some entry => writeOne entry outputDirectory
      | none => pure 2
  | ["host-verify", key, outputDirectory] =>
      match ← requireHostModuleEntry key with
      | some entry => verifyOne entry outputDirectory
      | none => pure 2
  | ["host-package-list"] =>
      printHostPackageList
      pure 0
  | ["host-package-write", key, outputDirectory] =>
      match ← requireHostRequest key with
      | some request => writeHostPackage request outputDirectory
      | none => pure 2
  | ["host-package-verify", key, outputDirectory] =>
      match ← requireHostRequest key with
      | some request => verifyHostPackage request outputDirectory
      | none => pure 2
  | ["host-claim-list"] =>
      printHostClaimList
      pure 0
  | ["host-claim-source", key] =>
      match ← requireHostClaimRequest key with
      | some request =>
          IO.println request.sourceEntry.source
          pure 0
      | none => pure 2
  | ["host-claim-write", key, outputDirectory] =>
      match ← requireHostClaimRequest key with
      | some request => writeHostClaimPackage request outputDirectory
      | none => pure 2
  | ["host-claim-verify", key, outputDirectory] =>
      match ← requireHostClaimRequest key with
      | some request => verifyHostClaimPackage request outputDirectory
      | none => pure 2
  | ["host-claim-verify-all", outputDirectory] =>
      verifyAllHostClaimPackages outputDirectory
  | ["host-suite-list"] =>
      printHostAnalysisSuiteList
      pure 0
  | ["host-suite-write", key, outputDirectory] =>
      match ← requireHostAnalysisSuiteRequest key with
      | some request => writeHostAnalysisSuitePackage request outputDirectory
      | none => pure 2
  | ["host-suite-verify", key, outputDirectory] =>
      match ← requireHostAnalysisSuiteRequest key with
      | some request => verifyHostAnalysisSuitePackage request outputDirectory
      | none => pure 2
  | ["host-analysis-list"] =>
      printHostMoleculeAnalysisList
      pure 0
  | ["host-analysis-write", key, outputDirectory] =>
      match ← requireHostMoleculeAnalysisRequest key with
      | some request => writeHostMoleculeAnalysisPackage request outputDirectory
      | none => pure 2
  | ["host-analysis-verify", key, outputDirectory] =>
      match ← requireHostMoleculeAnalysisRequest key with
      | some request => verifyHostMoleculeAnalysisPackage request outputDirectory
      | none => pure 2
  | ["assign-file", path] => do
      let contents ← IO.FS.readFile path
      let mut failures : Nat := 0
      for rawLine in contents.splitOn "\n" do
        let blank : Char → Bool := fun c => c == ' ' || c == '\t' || c == '\r'
        let line :=
          String.ofList (((rawLine.toList.dropWhile blank).reverse.dropWhile blank).reverse)
        if line.isEmpty || line.startsWith "#" then
          pure ()
        else
          match OneCenter.analyzeSmiles line with
          | Except.error message =>
              failures := failures + 1
              IO.println (line ++ "\tparse error: " ++ message)
          | Except.ok [] =>
              IO.println (line ++ "\tno stereogenic units")
          | Except.ok assignments =>
              IO.println
                (line ++ "\t" ++
                  String.intercalate "; " (assignments.map OneCenter.StereoAssignment.label))
          (← IO.getStdout).flush
      if failures == 0 then pure 0 else pure 1
  | ["assign", smiles] =>
      match OneCenter.analyzeSmiles smiles with
      | Except.error message =>
          IO.eprintln ("parse error: " ++ message)
          pure 2
      | Except.ok [] =>
          IO.println "no stereogenic units found"
          pure 0
      | Except.ok assignments =>
          for assignment in assignments do
            IO.println assignment.label
          pure 0
  | _ =>
      IO.eprintln usage
      pure 2

end CLI
end TetraStereo

/-- Lake executable entry point. -/
def main (args : List String) : IO UInt32 :=
  TetraStereo.CLI.main args
