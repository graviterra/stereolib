import TetraStereo.Engine.HostClaimCompiler

set_option autoImplicit false

namespace TetraStereo
namespace Examples
namespace HostClaimCompiler

open Engine

noncomputable section

/-!
  Checked fixtures for the broad host stereochemical claim compiler.

  These requests are typed: the host chooses from `HostStereoClaimTarget`, and Lean derives the
  theorem statement, proof, artifact, and generated source.  This is the first package surface that
  reaches across official-CIP, multi-center, graph-level, non-tetrahedral, conformational, and
  ensemble theorem families without accepting raw theorem/proof strings from the host.
-/

/-- Generated package for official-CIP assignment safety. -/
def officialCIPClaimRequest : HostStereoClaimRequest where
  target := HostStereoClaimTarget.officialCIPAssignmentSuccessResolved

/-- Generated package for multi-center relation classification. -/
def multiCenterRelationClaimRequest : HostStereoClaimRequest where
  target := HostStereoClaimTarget.multiCenterCipRSClassificationExactlyOne

/-- Generated package for graph-level descriptor classifier soundness. -/
def graphClassificationClaimRequest : HostStereoClaimRequest where
  target := HostStereoClaimTarget.graphDescriptorClassifierSound

/-- Generated package for graph-level unresolved-priority refusal. -/
def graphClassificationRefusalClaimRequest : HostStereoClaimRequest where
  target := HostStereoClaimTarget.graphDescriptorClassifierRefusesUnresolved

/-- Generated package for non-tetrahedral mirror-involution semantics. -/
def stereoElementMirrorClaimRequest : HostStereoClaimRequest where
  target := HostStereoClaimTarget.stereoElementProfileMirrorInvolutive

/-- Generated package for conformational profile chirality. -/
def conformationalClaimRequest : HostStereoClaimRequest where
  target := HostStereoClaimTarget.conformationalProfileChiralRefutesAchiral

/-- Generated package for ensemble descriptor chirality. -/
def ensembleClaimRequest : HostStereoClaimRequest where
  target := HostStereoClaimTarget.descriptorChiralEnsembleRefutesAchiral

/-- All broad host claim requests currently exposed as package fixtures. -/
def hostStereoClaimRequests : List HostStereoClaimRequest :=
  [ officialCIPClaimRequest
  , multiCenterRelationClaimRequest
  , graphClassificationClaimRequest
  , graphClassificationRefusalClaimRequest
  , stereoElementMirrorClaimRequest
  , conformationalClaimRequest
  , ensembleClaimRequest
  ]

/-- The broad host claim compiler currently covers seven theorem-family targets. -/
theorem hostStereoClaimRequests_length :
    hostStereoClaimRequests.length = 7 :=
  rfl

/-- Every broad host claim request produces a checked artifact before source generation. -/
theorem hostStereoClaimRequests_checked :
    ∀ request, request ∈ hostStereoClaimRequests → request.artifact.claim := by
  intro request _hmem
  exact request.artifact.proof

/-- The non-tetrahedral generated package target is the mirror-involution theorem family. -/
theorem stereoElementMirrorClaimRequest_target :
    stereoElementMirrorClaimRequest.target =
      HostStereoClaimTarget.stereoElementProfileMirrorInvolutive :=
  rfl

/-- The graph-refusal generated package is represented as a refusal artifact. -/
theorem graphClassificationRefusalClaimRequest_reason :
    graphClassificationRefusalClaimRequest.target.refusalReason? =
      some PublicClaimRefusalReason.unresolvedDependencies :=
  rfl

end
end HostClaimCompiler
end Examples
end TetraStereo
