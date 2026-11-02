import TetraStereo.Engine.Claims

set_option autoImplicit false

namespace TetraStereo
namespace Examples
namespace EngineClaims

open OneCenter

noncomputable section

/-!
  Checked examples for the broad public claim-transaction surface.

  These are not new chemistry examples.  They are public engine certificates that expose existing
  theorem families through one uniform transaction shape.
-/

def officialCIPClaimPlan : Engine.PublicClaimTheoremPlan where
  imports := ["TetraStereo.Engine.Claims"]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "official_cip_assignment_success_implies_resolved"
  statement := "TetraStereo.Engine.officialCIPAssignmentSuccessResolvedClaim.{0}"
  proofTerm := "  exact TetraStereo.Engine.officialCIPAssignmentSuccessResolvedClaim_holds.{0}"

def officialCIPClaimCertificate : Engine.CertifiedPublicClaim where
  kind := Engine.PublicClaimKind.officialCIPAssignment
  title := "success implies resolved official priorities"
  claim := Engine.officialCIPAssignmentSuccessResolvedClaim.{0}
  proof := Engine.officialCIPAssignmentSuccessResolvedClaim_holds.{0}
  theoremPlan := officialCIPClaimPlan
  artifact :=
    Engine.compilePublicClaim officialCIPClaimPlan
      Engine.PublicClaimKind.officialCIPAssignment
      "success implies resolved official priorities"
      Engine.officialCIPAssignmentSuccessResolvedClaim.{0}
      Engine.officialCIPAssignmentSuccessResolvedClaim_holds.{0}
  artifact_eq := rfl

theorem officialCIPClaimCertificate_checked :
    officialCIPClaimCertificate.artifact.claim :=
  officialCIPClaimCertificate.artifact_checked

def multiCenterRelationClaimPlan : Engine.PublicClaimTheoremPlan where
  imports := ["TetraStereo.Engine.Claims"]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "multi_center_cip_rs_relations_exactly_one"
  statement := "TetraStereo.Engine.multiCenterCipRSClassificationExactlyOneClaim.{0}"
  proofTerm := "  exact TetraStereo.Engine.multiCenterCipRSClassificationExactlyOneClaim_holds.{0}"

def multiCenterRelationClaimCertificate : Engine.CertifiedPublicClaim where
  kind := Engine.PublicClaimKind.multiCenterRelation
  title := "CIP R/S relations are exactly-one classified"
  claim := Engine.multiCenterCipRSClassificationExactlyOneClaim.{0}
  proof := Engine.multiCenterCipRSClassificationExactlyOneClaim_holds.{0}
  theoremPlan := multiCenterRelationClaimPlan
  artifact :=
    Engine.compilePublicClaim multiCenterRelationClaimPlan
      Engine.PublicClaimKind.multiCenterRelation
      "CIP R/S relations are exactly-one classified"
      Engine.multiCenterCipRSClassificationExactlyOneClaim.{0}
      Engine.multiCenterCipRSClassificationExactlyOneClaim_holds.{0}
  artifact_eq := rfl

theorem multiCenterRelationClaimCertificate_checked :
    multiCenterRelationClaimCertificate.artifact.claim :=
  multiCenterRelationClaimCertificate.artifact_checked

def graphClassificationClaimPlan : Engine.PublicClaimTheoremPlan where
  imports := ["TetraStereo.Engine.Claims"]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "graph_descriptor_classifier_sound"
  statement := "TetraStereo.Engine.graphDescriptorClassifierSoundClaim.{0}"
  proofTerm := "  exact TetraStereo.Engine.graphDescriptorClassifierSoundClaim_holds.{0}"

def graphClassificationClaimCertificate : Engine.CertifiedPublicClaim where
  kind := Engine.PublicClaimKind.graphClassification
  title := "descriptor classifier soundness"
  claim := Engine.graphDescriptorClassifierSoundClaim.{0}
  proof := Engine.graphDescriptorClassifierSoundClaim_holds.{0}
  theoremPlan := graphClassificationClaimPlan
  artifact :=
    Engine.compilePublicClaim graphClassificationClaimPlan
      Engine.PublicClaimKind.graphClassification
      "descriptor classifier soundness"
      Engine.graphDescriptorClassifierSoundClaim.{0}
      Engine.graphDescriptorClassifierSoundClaim_holds.{0}
  artifact_eq := rfl

theorem graphClassificationClaimCertificate_checked :
    graphClassificationClaimCertificate.artifact.claim :=
  graphClassificationClaimCertificate.artifact_checked

def graphClassificationRefusalPlan : Engine.PublicClaimTheoremPlan where
  imports := ["TetraStereo.Engine.Claims"]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "graph_descriptor_classifier_refuses_unresolved"
  statement := "TetraStereo.Engine.graphDescriptorClassifierRefusesUnresolvedClaim.{0}"
  proofTerm := "  exact TetraStereo.Engine.graphDescriptorClassifierRefusesUnresolvedClaim_holds.{0}"

def graphClassificationRefusalCertificate : Engine.CertifiedPublicClaimRefusal where
  kind := Engine.PublicClaimKind.graphClassification
  reason := Engine.PublicClaimRefusalReason.unresolvedDependencies
  title := "descriptor classifier refuses unresolved priorities"
  claim := Engine.graphDescriptorClassifierRefusesUnresolvedClaim.{0}
  proof := Engine.graphDescriptorClassifierRefusesUnresolvedClaim_holds.{0}
  theoremPlan := graphClassificationRefusalPlan
  artifact :=
    Engine.compilePublicClaimRefusal graphClassificationRefusalPlan
      Engine.PublicClaimKind.graphClassification
      Engine.PublicClaimRefusalReason.unresolvedDependencies
      "descriptor classifier refuses unresolved priorities"
      Engine.graphDescriptorClassifierRefusesUnresolvedClaim.{0}
      Engine.graphDescriptorClassifierRefusesUnresolvedClaim_holds.{0}
  artifact_eq := rfl

theorem graphClassificationRefusalCertificate_checked :
    graphClassificationRefusalCertificate.artifact.claim :=
  graphClassificationRefusalCertificate.artifact_checked

def stereoElementClaimPlan : Engine.PublicClaimTheoremPlan where
  imports := ["TetraStereo.Engine.Claims"]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "stereo_element_profile_mirror_involutive"
  statement := "TetraStereo.Engine.stereoElementProfileMirrorInvolutiveClaim.{0}"
  proofTerm := "  exact TetraStereo.Engine.stereoElementProfileMirrorInvolutiveClaim_holds.{0}"

def stereoElementClaimCertificate : Engine.CertifiedPublicClaim where
  kind := Engine.PublicClaimKind.nonTetrahedralDescriptor
  title := "profile mirror semantics are involutive"
  claim := Engine.stereoElementProfileMirrorInvolutiveClaim.{0}
  proof := Engine.stereoElementProfileMirrorInvolutiveClaim_holds.{0}
  theoremPlan := stereoElementClaimPlan
  artifact :=
    Engine.compilePublicClaim stereoElementClaimPlan
      Engine.PublicClaimKind.nonTetrahedralDescriptor
      "profile mirror semantics are involutive"
      Engine.stereoElementProfileMirrorInvolutiveClaim.{0}
      Engine.stereoElementProfileMirrorInvolutiveClaim_holds.{0}
  artifact_eq := rfl

theorem stereoElementClaimCertificate_checked :
    stereoElementClaimCertificate.artifact.claim :=
  stereoElementClaimCertificate.artifact_checked

def conformationalClaimPlan : Engine.PublicClaimTheoremPlan where
  imports := ["TetraStereo.Engine.Claims"]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "conformational_profile_chiral_refutes_achiral"
  statement := "TetraStereo.Engine.conformationalProfileChiralRefutesAchiralClaim.{0}"
  proofTerm := "  exact TetraStereo.Engine.conformationalProfileChiralRefutesAchiralClaim_holds.{0}"

def conformationalClaimCertificate : Engine.CertifiedPublicClaim where
  kind := Engine.PublicClaimKind.conformationalEnsemble
  title := "profile chirality refutes ensemble achirality"
  claim := Engine.conformationalProfileChiralRefutesAchiralClaim.{0}
  proof := Engine.conformationalProfileChiralRefutesAchiralClaim_holds.{0}
  theoremPlan := conformationalClaimPlan
  artifact :=
    Engine.compilePublicClaim conformationalClaimPlan
      Engine.PublicClaimKind.conformationalEnsemble
      "profile chirality refutes ensemble achirality"
      Engine.conformationalProfileChiralRefutesAchiralClaim.{0}
      Engine.conformationalProfileChiralRefutesAchiralClaim_holds.{0}
  artifact_eq := rfl

theorem conformationalClaimCertificate_checked :
    conformationalClaimCertificate.artifact.claim :=
  conformationalClaimCertificate.artifact_checked

def ensembleClaimPlan : Engine.PublicClaimTheoremPlan where
  imports := ["TetraStereo.Engine.Claims"]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "descriptor_chiral_ensemble_refutes_achiral"
  statement := "TetraStereo.Engine.descriptorChiralEnsembleRefutesAchiralClaim.{0}"
  proofTerm := "  exact TetraStereo.Engine.descriptorChiralEnsembleRefutesAchiralClaim_holds.{0}"

def ensembleClaimCertificate : Engine.CertifiedPublicClaim where
  kind := Engine.PublicClaimKind.conformationalEnsemble
  title := "descriptor-chiral ensemble refutes descriptor-achiral ensemble"
  claim := Engine.descriptorChiralEnsembleRefutesAchiralClaim.{0}
  proof := Engine.descriptorChiralEnsembleRefutesAchiralClaim_holds.{0}
  theoremPlan := ensembleClaimPlan
  artifact :=
    Engine.compilePublicClaim ensembleClaimPlan
      Engine.PublicClaimKind.conformationalEnsemble
      "descriptor-chiral ensemble refutes descriptor-achiral ensemble"
      Engine.descriptorChiralEnsembleRefutesAchiralClaim.{0}
      Engine.descriptorChiralEnsembleRefutesAchiralClaim_holds.{0}
  artifact_eq := rfl

theorem ensembleClaimCertificate_checked :
    ensembleClaimCertificate.artifact.claim :=
  ensembleClaimCertificate.artifact_checked

def publicClaimCertificates : List Engine.CertifiedPublicClaim :=
  [ officialCIPClaimCertificate
  , multiCenterRelationClaimCertificate
  , graphClassificationClaimCertificate
  , stereoElementClaimCertificate
  , conformationalClaimCertificate
  , ensembleClaimCertificate
  ]

def publicClaimRefusalCertificates : List Engine.CertifiedPublicClaimRefusal :=
  [graphClassificationRefusalCertificate]

end
end EngineClaims
end Examples
end TetraStereo
