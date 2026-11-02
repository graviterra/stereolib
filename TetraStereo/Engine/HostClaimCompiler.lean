import TetraStereo.Engine.HostModuleCompiler
import TetraStereo.Engine.Claims

set_option autoImplicit false

namespace TetraStereo
namespace Engine

open OneCenter

noncomputable section

/-!
  Broad host stereochemical claim compiler.

  `HostOfficialStereoRequest` compiles one molecule-shaped official-stereo query.  This module
  adds the next host-facing layer: a typed request for broad theorem-family claims.  The host picks
  a target from `HostStereoClaimTarget`; Lean derives the statement, proof term, public claim kind,
  theorem artifact, generated source, and package path without accepting raw theorem statements or
  raw proof source from the host.
-/

/-- Broad stereochemical theorem families that the host claim compiler can package. -/
inductive HostStereoClaimTarget where
  | officialCIPAssignmentSuccessResolved
  | multiCenterCipRSClassificationExactlyOne
  | graphDescriptorClassifierSound
  | graphDescriptorClassifierRefusesUnresolved
  | stereoElementProfileMirrorInvolutive
  | conformationalProfileChiralRefutesAchiral
  | descriptorChiralEnsembleRefutesAchiral
  deriving DecidableEq, Repr

namespace HostStereoClaimTarget

/-- All broad stereochemical theorem-family targets currently exposed to host packages. -/
def all : List HostStereoClaimTarget :=
  [ officialCIPAssignmentSuccessResolved
  , multiCenterCipRSClassificationExactlyOne
  , graphDescriptorClassifierSound
  , graphDescriptorClassifierRefusesUnresolved
  , stereoElementProfileMirrorInvolutive
  , conformationalProfileChiralRefutesAchiral
  , descriptorChiralEnsembleRefutesAchiral
  ]

/-- Public claim kind associated with this host target. -/
def kind : HostStereoClaimTarget → PublicClaimKind
  | officialCIPAssignmentSuccessResolved => PublicClaimKind.officialCIPAssignment
  | multiCenterCipRSClassificationExactlyOne => PublicClaimKind.multiCenterRelation
  | graphDescriptorClassifierSound => PublicClaimKind.graphClassification
  | graphDescriptorClassifierRefusesUnresolved => PublicClaimKind.graphClassification
  | stereoElementProfileMirrorInvolutive => PublicClaimKind.nonTetrahedralDescriptor
  | conformationalProfileChiralRefutesAchiral => PublicClaimKind.conformationalEnsemble
  | descriptorChiralEnsembleRefutesAchiral => PublicClaimKind.conformationalEnsemble

/-- Whether this target is a refusal-family claim. -/
def refusalReason? : HostStereoClaimTarget → Option PublicClaimRefusalReason
  | graphDescriptorClassifierRefusesUnresolved =>
      some PublicClaimRefusalReason.unresolvedDependencies
  | _ => none

/-- Human-readable title for this target. -/
def title : HostStereoClaimTarget → String
  | officialCIPAssignmentSuccessResolved => "success implies resolved official priorities"
  | multiCenterCipRSClassificationExactlyOne => "CIP R/S relations are exactly-one classified"
  | graphDescriptorClassifierSound => "descriptor classifier soundness"
  | graphDescriptorClassifierRefusesUnresolved =>
      "descriptor classifier refuses unresolved priorities"
  | stereoElementProfileMirrorInvolutive => "profile mirror semantics are involutive"
  | conformationalProfileChiralRefutesAchiral =>
      "profile chirality refutes ensemble achirality"
  | descriptorChiralEnsembleRefutesAchiral =>
      "descriptor-chiral ensemble refutes descriptor-achiral ensemble"

/-- The theorem-family proposition represented by this target. -/
def claim : HostStereoClaimTarget → Prop
  | officialCIPAssignmentSuccessResolved =>
      officialCIPAssignmentSuccessResolvedClaim.{0}
  | multiCenterCipRSClassificationExactlyOne =>
      multiCenterCipRSClassificationExactlyOneClaim.{0}
  | graphDescriptorClassifierSound =>
      graphDescriptorClassifierSoundClaim.{0}
  | graphDescriptorClassifierRefusesUnresolved =>
      graphDescriptorClassifierRefusesUnresolvedClaim.{0}
  | stereoElementProfileMirrorInvolutive =>
      stereoElementProfileMirrorInvolutiveClaim.{0}
  | conformationalProfileChiralRefutesAchiral =>
      conformationalProfileChiralRefutesAchiralClaim.{0}
  | descriptorChiralEnsembleRefutesAchiral =>
      descriptorChiralEnsembleRefutesAchiralClaim.{0}

/-- Checked proof for this target's theorem-family proposition. -/
def proof (target : HostStereoClaimTarget) : target.claim :=
  match target with
  | officialCIPAssignmentSuccessResolved =>
      officialCIPAssignmentSuccessResolvedClaim_holds.{0}
  | multiCenterCipRSClassificationExactlyOne =>
      multiCenterCipRSClassificationExactlyOneClaim_holds.{0}
  | graphDescriptorClassifierSound =>
      graphDescriptorClassifierSoundClaim_holds.{0}
  | graphDescriptorClassifierRefusesUnresolved =>
      graphDescriptorClassifierRefusesUnresolvedClaim_holds.{0}
  | stereoElementProfileMirrorInvolutive =>
      stereoElementProfileMirrorInvolutiveClaim_holds.{0}
  | conformationalProfileChiralRefutesAchiral =>
      conformationalProfileChiralRefutesAchiralClaim_holds.{0}
  | descriptorChiralEnsembleRefutesAchiral =>
      descriptorChiralEnsembleRefutesAchiralClaim_holds.{0}

/-- Rendered theorem statement for generated source. -/
def statement : HostStereoClaimTarget → String
  | officialCIPAssignmentSuccessResolved =>
      "TetraStereo.Engine.officialCIPAssignmentSuccessResolvedClaim.{0}"
  | multiCenterCipRSClassificationExactlyOne =>
      "TetraStereo.Engine.multiCenterCipRSClassificationExactlyOneClaim.{0}"
  | graphDescriptorClassifierSound =>
      "TetraStereo.Engine.graphDescriptorClassifierSoundClaim.{0}"
  | graphDescriptorClassifierRefusesUnresolved =>
      "TetraStereo.Engine.graphDescriptorClassifierRefusesUnresolvedClaim.{0}"
  | stereoElementProfileMirrorInvolutive =>
      "TetraStereo.Engine.stereoElementProfileMirrorInvolutiveClaim.{0}"
  | conformationalProfileChiralRefutesAchiral =>
      "TetraStereo.Engine.conformationalProfileChiralRefutesAchiralClaim.{0}"
  | descriptorChiralEnsembleRefutesAchiral =>
      "TetraStereo.Engine.descriptorChiralEnsembleRefutesAchiralClaim.{0}"

/-- Rendered proof term for generated source. -/
def proofTerm : HostStereoClaimTarget → String
  | officialCIPAssignmentSuccessResolved =>
      "  exact TetraStereo.Engine.officialCIPAssignmentSuccessResolvedClaim_holds.{0}"
  | multiCenterCipRSClassificationExactlyOne =>
      "  exact TetraStereo.Engine.multiCenterCipRSClassificationExactlyOneClaim_holds.{0}"
  | graphDescriptorClassifierSound =>
      "  exact TetraStereo.Engine.graphDescriptorClassifierSoundClaim_holds.{0}"
  | graphDescriptorClassifierRefusesUnresolved =>
      "  exact TetraStereo.Engine.graphDescriptorClassifierRefusesUnresolvedClaim_holds.{0}"
  | stereoElementProfileMirrorInvolutive =>
      "  exact TetraStereo.Engine.stereoElementProfileMirrorInvolutiveClaim_holds.{0}"
  | conformationalProfileChiralRefutesAchiral =>
      "  exact TetraStereo.Engine.conformationalProfileChiralRefutesAchiralClaim_holds.{0}"
  | descriptorChiralEnsembleRefutesAchiral =>
      "  exact TetraStereo.Engine.descriptorChiralEnsembleRefutesAchiralClaim_holds.{0}"

/-- Default file basename for this target. -/
def defaultFileName : HostStereoClaimTarget → String
  | officialCIPAssignmentSuccessResolved => "HostOfficialCIPAssignmentClaim.lean"
  | multiCenterCipRSClassificationExactlyOne => "HostMultiCenterRelationClaim.lean"
  | graphDescriptorClassifierSound => "HostGraphClassificationSoundClaim.lean"
  | graphDescriptorClassifierRefusesUnresolved => "HostGraphClassificationRefusalClaim.lean"
  | stereoElementProfileMirrorInvolutive => "HostStereoElementMirrorClaim.lean"
  | conformationalProfileChiralRefutesAchiral => "HostConformationalClaim.lean"
  | descriptorChiralEnsembleRefutesAchiral => "HostEnsembleClaim.lean"

/-- Default theorem name for this target. -/
def defaultTheoremName : HostStereoClaimTarget → String
  | officialCIPAssignmentSuccessResolved => "host_official_cip_assignment_success_resolved"
  | multiCenterCipRSClassificationExactlyOne => "host_multi_center_cip_rs_exactly_one"
  | graphDescriptorClassifierSound => "host_graph_descriptor_classifier_sound"
  | graphDescriptorClassifierRefusesUnresolved => "host_graph_descriptor_classifier_refuses"
  | stereoElementProfileMirrorInvolutive => "host_stereo_element_mirror_involutive"
  | conformationalProfileChiralRefutesAchiral =>
      "host_conformational_profile_chiral_refutes_achiral"
  | descriptorChiralEnsembleRefutesAchiral =>
      "host_descriptor_chiral_ensemble_refutes_achiral"

/-- Default host-facing key for this target. -/
def defaultKey : HostStereoClaimTarget → String
  | officialCIPAssignmentSuccessResolved => "host-claim-official-cip"
  | multiCenterCipRSClassificationExactlyOne => "host-claim-multicenter-relation"
  | graphDescriptorClassifierSound => "host-claim-graph-classification"
  | graphDescriptorClassifierRefusesUnresolved => "host-claim-graph-refusal"
  | stereoElementProfileMirrorInvolutive => "host-claim-stereo-element-mirror"
  | conformationalProfileChiralRefutesAchiral => "host-claim-conformational"
  | descriptorChiralEnsembleRefutesAchiral => "host-claim-ensemble"

/-- Default registry description for this target. -/
def defaultDescription (target : HostStereoClaimTarget) : String :=
  "generated broad host stereochemical claim: " ++ target.title

end HostStereoClaimTarget

/-- Host-facing request to package a broad theorem-family stereochemical claim. -/
structure HostStereoClaimRequest where
  target : HostStereoClaimTarget
  key : String := target.defaultKey
  description : String := target.defaultDescription
  fileName : String := target.defaultFileName
  namespacePath : List String := ["TetraStereoGenerated", "HostClaims"]
  theoremName : String := target.defaultTheoremName
  imports : List String := ["TetraStereo.Engine.Claims"]
  options : List String := ["set_option maxHeartbeats 1000000"]

namespace HostStereoClaimRequest


def theoremPlan (request : HostStereoClaimRequest) : PublicClaimTheoremPlan where
  imports := request.imports
  namespacePath := request.namespacePath
  theoremName := request.theoremName
  statement := request.target.statement
  proofTerm := request.target.proofTerm

/-- Compile this typed host claim request into a checked theorem artifact. -/
def artifact (request : HostStereoClaimRequest) : LeanCertificateArtifact :=
  match _h : request.target.refusalReason? with
  | some reason =>
      compilePublicClaimRefusal request.theoremPlan request.target.kind reason request.target.title
        request.target.claim request.target.proof
  | none =>
      compilePublicClaim request.theoremPlan request.target.kind request.target.title
        request.target.claim request.target.proof

/-- Source-registry entry for this typed host claim request. -/
def sourceEntry (request : HostStereoClaimRequest) : CertificateSourceEntry where
  key := request.key
  description := request.description
  fileName := request.fileName
  source := request.artifact.source

/-- Validate host-supplied metadata that affects generated source or paths. -/
def validateGeneratedShape (request : HostStereoClaimRequest) : Except String Unit := do
  validateNamespacePath "namespacePath" request.namespacePath
  validateModuleNames "imports" request.imports
  validateOptionLines "options" request.options
  validateGeneratedFileName "fileName" request.fileName
  validateLeanNames "generated theorem names" [request.theoremName]

/-- Source path for this generated broad-claim package under an output root. -/
def packageSourcePath (request : HostStereoClaimRequest) (packageRoot : String) :
    System.FilePath :=
  System.FilePath.mk
    (packageRoot ++ "/" ++ HostOfficialStereoRequest.pathStem request.namespacePath ++ "/" ++
      request.fileName)

/-- Write this generated broad-claim package to an import-independent Lean file. -/
def writePackageSource (request : HostStereoClaimRequest) (packageRoot : String) :
    IO System.FilePath := do
  match request.validateGeneratedShape with
  | Except.ok () => pure ()
  | Except.error message => throw (IO.userError message)
  let path := request.packageSourcePath packageRoot
  writeLeanSourceFile path request.sourceEntry.source

/-- Write and independently verify this generated broad-claim package. -/
def writeAndVerifyPackageSource (request : HostStereoClaimRequest) (packageRoot : String) :
    IO CertificateVerificationResult := do
  let path ← request.writePackageSource packageRoot
  verifyLeanCertificateFile path

end HostStereoClaimRequest

end
end Engine
end TetraStereo
