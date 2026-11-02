import TetraStereo.Engine.HostAnalysisSuiteCompiler
import TetraStereo.Examples.HostClaimCompiler
import TetraStereo.Examples.HostModuleCompiler

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace TetraStereo
namespace Examples
namespace HostAnalysisSuiteCompiler

open Engine

noncomputable section

/-!
  Checked fixture for the host analysis-suite compiler.

  The suite combines one molecule-shaped detector-backed official-stereo package with every broad
  host theorem-family package.  Generated output therefore contains real molecule-derived Lean
  source, broad Stereolib theorem-family source, and a manifest that imports and references them all.
-/

/-- Suite-owned view of the standalone helical host request. -/
def helicalBridgeSuiteOfficialRequest : HostOfficialStereoRequest :=
  { TetraStereo.Examples.HostModuleCompiler.compiledHelicalBridgeHostRequest with
    key :=
      hostScopedPackageKey "host-suite-helical-plus-broad-claims"
        "helical-bridge-official-stereo-comparison"
    ownerRequestKey := "host-suite-helical-plus-broad-claims"
    packageKeySuffix := "helical-bridge-official-stereo-comparison" }

/-- Suite-owned view of the standalone auto-bridge host request used by negative fixtures. -/
def autoBridgeSuiteOfficialRequest : HostOfficialStereoRequest :=
  { TetraStereo.Examples.HostModuleCompiler.compiledAutoBridgeHostRequest with
    key :=
      hostScopedPackageKey "host-suite-helical-plus-broad-claims"
        "auto-bridge-official-stereo-refusal"
    ownerRequestKey := "host-suite-helical-plus-broad-claims"
    packageKeySuffix := "auto-bridge-official-stereo-refusal" }

/-- End-to-end host analysis suite fixture: typed helical package plus all broad claims. -/
def helicalBridgeFullSuiteRequest : HostAnalysisSuiteRequest where
  key := "host-suite-helical-plus-broad-claims"
  description := "helical bridge official-stereo package plus broad Stereolib claim bundle"
  officialStereoRequests := [helicalBridgeSuiteOfficialRequest]
  claimRequests := TetraStereo.Examples.HostClaimCompiler.hostStereoClaimRequests
  namespacePath := ["TetraStereoGenerated", "Examples", "HostSuites", "HelicalBridgeFull"]
  fileName := "HelicalBridgeFullHostAnalysisSuite.lean"
  theoremName := "helical_bridge_full_host_analysis_suite_checked"

/-- The example suite contains one molecule-shaped official-stereo package. -/
theorem helicalBridgeFullSuiteRequest_official_count :
    helicalBridgeFullSuiteRequest.officialStereoRequests.length = 1 :=
  rfl

/-- Hand-assembled suite fixtures now bind official packages to the suite by exact owner metadata. -/
theorem helicalBridgeFullSuiteRequest_official_owner :
    helicalBridgeSuiteOfficialRequest.ownerRequestKey = "host-suite-helical-plus-broad-claims" :=
  rfl

/-- The example suite carries all seven broad theorem-family packages. -/
theorem helicalBridgeFullSuiteRequest_claim_count :
    helicalBridgeFullSuiteRequest.claimRequests.length = 7 :=
  rfl

/-- The suite manifest imports eight generated modules in total. -/
theorem helicalBridgeFullSuiteRequest_manifest_import_count :
    helicalBridgeFullSuiteRequest.manifestImportModules.length = 8 :=
  rfl

/-- Deliberately invalid suite whose manifest module would overwrite a generated claim module. -/
def collidingManifestSuiteRequest : HostAnalysisSuiteRequest :=
  { helicalBridgeFullSuiteRequest with
    namespacePath := ["TetraStereoGenerated", "HostClaims"]
    fileName := "HostOfficialCIPAssignmentClaim.lean" }

/-- Suite manifest/package module collisions are rejected before generated files are written. -/
theorem collidingManifestSuiteRequest_rejected :
    (match collidingManifestSuiteRequest.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by
    set_option maxRecDepth 100000 in
      decide

/-- Deliberately invalid suite with duplicate child package keys across official and claim packages. -/
def duplicateChildPackageKeySuiteRequest : HostAnalysisSuiteRequest :=
  { helicalBridgeFullSuiteRequest with
    officialStereoRequests :=
      [ { TetraStereo.Examples.HostModuleCompiler.compiledHelicalBridgeHostRequest with
          key := TetraStereo.Examples.HostClaimCompiler.officialCIPClaimRequest.key } ]
    claimRequests := [TetraStereo.Examples.HostClaimCompiler.officialCIPClaimRequest] }

/-- Direct suite requests reject duplicate child package keys across package families. -/
theorem duplicateChildPackageKeySuiteRequest_rejected :
    (match duplicateChildPackageKeySuiteRequest.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by
    set_option maxRecDepth 100000 in
      decide

/-- Deliberately invalid suite whose claim theorem collides with an imported host declaration. -/
def claimHostDeclarationCollisionSuiteRequest : HostAnalysisSuiteRequest :=
  { helicalBridgeFullSuiteRequest with
    officialStereoRequests :=
      [autoBridgeSuiteOfficialRequest]
    claimRequests :=
      [ { TetraStereo.Examples.HostClaimCompiler.officialCIPClaimRequest with
          namespacePath :=
            autoBridgeSuiteOfficialRequest.namespacePath
          fileName := "ClaimHostDeclarationCollision.lean"
          theoremName := autoBridgeSuiteOfficialRequest.rawName } ] }

/-- Claim theorem names that collide with imported host declarations are rejected. -/
theorem claimHostDeclarationCollisionSuiteRequest_rejected :
    (match claimHostDeclarationCollisionSuiteRequest.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by
    set_option maxRecDepth 100000 in
      decide

/-- Deliberately invalid suite whose manifest theorem duplicates an imported claim theorem. -/
def manifestTheoremCollisionSuiteRequest : HostAnalysisSuiteRequest :=
  { helicalBridgeFullSuiteRequest with
    officialStereoRequests := []
    claimRequests := [TetraStereo.Examples.HostClaimCompiler.officialCIPClaimRequest]
    namespacePath := TetraStereo.Examples.HostClaimCompiler.officialCIPClaimRequest.namespacePath
    fileName := "ManifestTheoremCollision.lean"
    theoremName := TetraStereo.Examples.HostClaimCompiler.officialCIPClaimRequest.theoremName }

/-- Manifest theorem names are checked against imported package theorem names. -/
theorem manifestTheoremCollisionSuiteRequest_rejected :
    (match manifestTheoremCollisionSuiteRequest.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by
    set_option maxRecDepth 100000 in
      decide

end
end HostAnalysisSuiteCompiler
end Examples
end TetraStereo
