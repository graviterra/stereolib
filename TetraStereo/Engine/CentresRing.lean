import TetraStereo.Engine.CentresRingReplay

set_option autoImplicit false

namespace TetraStereo.Engine.CentresRing
open OneCenter CertifiedLocalizedCIPInput
open LocalizedGenericMarkedRecalculation (frameAtoms? readback?)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedChemicalRing (Input Report coordinatesAdmitted)

def request (input : Input) (centers : List Nat := inventory input) : Except String String := do
  unless coordinatesAdmitted input do throw "coordinate admission failed"
  unless decide centers.Nodup && centers.all (inventory input).contains do throw "invalid center inventory"
  let mol := input.molecule
  let atoms := mol.atoms.map fun a =>
    s!"a {a.element.atomicNumber} {a.isotope?.getD 0} {a.charge}"
  let bonds := mol.bonds.map fun b => s!"b {b.source} {b.target}"
  let frames ← centers.mapM fun atom => do
    let some ids := frameAtoms? mol (canonicalCenterRoot atom) | throw "missing frame"
    let some hand := readback? (inputGeometry input.certified) ids | throw "degenerate frame"
    let parity := if hand == .R then "R" else "S"
    return s!"f {atom} {parity} {String.intercalate " " (ids.map toString)}"
  return String.intercalate "\n" (["centres-1.0"] ++ atoms ++ bonds ++ frames) ++ "\n"

structure Result (input : Input) (centers : List Nat := inventory input) where
  traces : List CenterTrace
  report : Report
  checked : ValidReport input centers traces report

def releaseCommit : String := "aaed608ee1d917fcd5f72964d9ca6227bd790804"

structure Receipt where
  release : String
  molecularRequest : String
  traces : List CenterTrace
  deriving Lean.FromJson, Lean.ToJson

def Result.receipt {input centers} (r : Result input centers) : Except String Receipt := do
  return ⟨releaseCommit, ← request input centers, r.traces⟩

/-- Offline replay binds atom properties, bond order in the request, ordered
centers, carrier identities and local handedness to the caller's input.
Comparison values are externally supplied observations. -/
def checkReceipt (input : Input) (packet : Receipt) (centers : List Nat := inventory input) :
    Except String (Result input centers) := do
  unless packet.release == releaseCommit do throw "wrong baseline release"
  unless packet.molecularRequest == (← request input centers) do throw "molecular request mismatch"
  let rows ← verify input packet.traces centers
  return ⟨packet.traces,rows.1,rows.2⟩

-- The bounded module cache keys on this Lean source. Keep these input fingerprints
-- synchronized when either embedded file changes. The release test checks both.
-- run_pinned.py SHA-256 501208b035db5034c4f9d1d98a6f88e4b35f182f735739adb4be035d24603e10
-- release-1.0.json SHA-256 8223bd2ce2dfd080bc2269f6790341ed589deffbd88577b7d8055b9af5608b5f
private def runner : String := include_str "../../tools/centres10/run_pinned.py"
private def classManifest : String := include_str "../../tools/centres10/release-1.0.json"

/-- Run the release checker on the configured classes and dependency. The JVM
loads private copies of the verified bytes. Reject diagnostics or malformed JSON. -/
def runCore (input : Input) (centers : List Nat) (classpath : String) (prefixes : Bool) :
    IO (Except String Lean.Json) := do
  let data ← match request input centers with
    | .error msg => return .error msg
    | .ok text => pure text
  let program := "PINNED_RELEASE = " ++ classManifest ++ "\n" ++ runner
  let args := #["-I","-c",program,classpath] ++ (if prefixes then #["--rule-prefixes"] else #[])
  let out ← try IO.Process.output {cmd := "/usr/bin/python3", args} (some data)
    catch err => return .error s!"cannot execute Centres: {err}"
  if out.exitCode != 0 || !out.stderr.isEmpty then
    return .error s!"Centres exited {out.exitCode}: {out.stderr.trimAscii}"
  return Lean.Json.parse out.stdout

/-- Run the pinned 2018 core, then replay every root and scheduled auxiliary sort
and verify the reported labels against the original uninstrumented run. -/
def analyze (input : Input)
    (centers : List Nat := inventory input)
    (classpath : String := ".cache/centres10/classes:.cache/centres10/guava.jar") :
    IO (Except String (Result input centers)) := do
  let parsed ← runCore input centers classpath false
  return do
    let json ← parsed
    let traces : List CenterTrace ← Lean.fromJson? json
    let rows ← verify input traces centers
    return ⟨traces,rows.1,rows.2⟩

end TetraStereo.Engine.CentresRing
assert_kernel_only TetraStereo.Engine.CentresRing.checkReceipt
