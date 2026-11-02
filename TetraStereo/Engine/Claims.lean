import TetraStereo.Engine.Result
import TetraStereo.OneCenter.GraphStereoPipeline
import TetraStereo.OneCenter.StereochemicalElements

set_option autoImplicit false

namespace TetraStereo
namespace Engine

open OneCenter

noncomputable section

/-!
  Public claim transactions for the wider stereochemistry engine.

  One-center `R/S` now has dedicated success/refusal transactions.  This module exposes the same
  proof-carrying shape for broader stereochemical outputs: official CIP assignments, multi-center
  relations, graph-level classifications, non-tetrahedral descriptor algebra, and
  conformational/ensemble claims.
-/

/-- Public-facing classes of stereochemical claims carried by the engine. -/
inductive PublicClaimKind where
  | officialCIPAssignment
  | multiCenterRelation
  | graphClassification
  | nonTetrahedralDescriptor
  | conformationalEnsemble
  | generic
  deriving DecidableEq, Repr

namespace PublicClaimKind

/-- Host-facing label for a public claim kind. -/
def label : PublicClaimKind → String
  | officialCIPAssignment => "official CIP assignment"
  | multiCenterRelation => "multi-center relation"
  | graphClassification => "graph-level classification"
  | nonTetrahedralDescriptor => "non-tetrahedral descriptor"
  | conformationalEnsemble => "conformational/ensemble stereochemistry"
  | generic => "generic stereochemical claim"

end PublicClaimKind

/-- Public-facing reasons why a broad stereochemical claim transaction may refuse. -/
inductive PublicClaimRefusalReason where
  | unresolvedDependencies
  | unsupportedStereoElement
  | unsupportedGraphClassifier
  | unsupportedConformationalPolicy
  | unsupportedOfficialCIPContext
  deriving DecidableEq, Repr

namespace PublicClaimRefusalReason

/-- Host-facing label for a public claim refusal. -/
def label : PublicClaimRefusalReason → String
  | unresolvedDependencies => "unresolved stereochemical dependencies"
  | unsupportedStereoElement => "unsupported stereochemical element"
  | unsupportedGraphClassifier => "unsupported graph classifier"
  | unsupportedConformationalPolicy => "unsupported conformational policy"
  | unsupportedOfficialCIPContext => "unsupported official CIP context"

end PublicClaimRefusalReason


structure PublicClaimTheoremPlan where
  imports : List String := ["TetraStereo.Engine.Claims"]
  namespacePath : List String := ["TetraStereo", "Generated"]
  theoremName : String
  statement : String
  proofTerm : String

namespace PublicClaimTheoremPlan


def toTheoremExport (plan : PublicClaimTheoremPlan) : LeanTheoremExport where
  imports := plan.imports
  namespacePath := plan.namespacePath
  theoremName := plan.theoremName
  statement := plan.statement
  proofTerm := plan.proofTerm

end PublicClaimTheoremPlan

/-- Compile a checked public stereochemical claim into a theorem artifact. -/
def compilePublicClaim (plan : PublicClaimTheoremPlan) (kind : PublicClaimKind)
    (title : String) (claim : Prop) (proof : claim) : LeanCertificateArtifact where
  kind := LeanCertificateKind.stereoClaim
  title := "Public engine " ++ kind.label ++ ": " ++ title
  theoremExport := plan.toTheoremExport
  claim := claim
  proof := proof

/-- Compile a checked public stereochemical refusal claim into a theorem artifact. -/
def compilePublicClaimRefusal (plan : PublicClaimTheoremPlan) (kind : PublicClaimKind)
    (reason : PublicClaimRefusalReason) (title : String) (claim : Prop) (proof : claim) :
    LeanCertificateArtifact where
  kind := LeanCertificateKind.stereoClaimRefusal
  title := "Public engine " ++ kind.label ++ " refusal: " ++ reason.label ++ " — " ++ title
  theoremExport := plan.toTheoremExport
  claim := claim
  proof := proof

/-- A checked public stereochemical claim plus its theorem artifact. -/
structure CertifiedPublicClaim where
  kind : PublicClaimKind
  title : String
  claim : Prop
  proof : claim
  theoremPlan : PublicClaimTheoremPlan
  artifact : LeanCertificateArtifact
  artifact_eq : artifact = compilePublicClaim theoremPlan kind title claim proof

namespace CertifiedPublicClaim

/-- The public claim artifact is checked by construction. -/
theorem artifact_checked (certificate : CertifiedPublicClaim) :
    certificate.artifact.claim := by
  rw [certificate.artifact_eq]
  exact
    (compilePublicClaim certificate.theoremPlan certificate.kind certificate.title
      certificate.claim certificate.proof).checked

end CertifiedPublicClaim

/-- A checked public stereochemical refusal plus its theorem artifact. -/
structure CertifiedPublicClaimRefusal where
  kind : PublicClaimKind
  reason : PublicClaimRefusalReason
  title : String
  claim : Prop
  proof : claim
  theoremPlan : PublicClaimTheoremPlan
  artifact : LeanCertificateArtifact
  artifact_eq :
    artifact = compilePublicClaimRefusal theoremPlan kind reason title claim proof

namespace CertifiedPublicClaimRefusal

/-- The public refusal artifact is checked by construction. -/
theorem artifact_checked (refusal : CertifiedPublicClaimRefusal) :
    refusal.artifact.claim := by
  rw [refusal.artifact_eq]
  exact
    (compilePublicClaimRefusal refusal.theoremPlan refusal.kind refusal.reason refusal.title
      refusal.claim refusal.proof).checked

end CertifiedPublicClaimRefusal

/-- Total public transaction shape for broad stereochemical claims. -/
inductive PublicClaimDecision where
  | certified (certificate : CertifiedPublicClaim)
  | refused (refusal : CertifiedPublicClaimRefusal)

namespace PublicClaimDecision

/-- The checked proposition carried by this public claim decision. -/
def artifactClaim : PublicClaimDecision → Prop
  | certified certificate => certificate.artifact.claim
  | refused refusal => refusal.artifact.claim

/-- Every public claim decision carries a checked theorem artifact. -/
theorem artifact_checked (decision : PublicClaimDecision) : decision.artifactClaim := by
  cases decision with
  | certified certificate => exact certificate.artifact_checked
  | refused refusal => exact refusal.artifact_checked

end PublicClaimDecision

/-! ### Generic public claim spines for existing theorem families -/

/-- Public claim: official one-center `R/S` success implies resolved official priorities. -/
def officialCIPAssignmentSuccessResolvedClaim : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (g : TetrahedralGeometry.Realization)
    (_ : CertifiedOfficialRSAssignment m context g),
      m.ResolvedOfficialCIP context

theorem officialCIPAssignmentSuccessResolvedClaim_holds :
    officialCIPAssignmentSuccessResolvedClaim := by
  intro V _ _ m context g assignment
  exact assignment.resolved

/-- Public claim: multi-center CIP `R/S` configuration relations are exactly-one classified. -/
def multiCenterCipRSClassificationExactlyOneClaim : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (cfg₁ cfg₂ : m.Configuration),
      m.CipRSConfigurationClassificationExactlyOne cfg₁ cfg₂

theorem multiCenterCipRSClassificationExactlyOneClaim_holds :
    multiCenterCipRSClassificationExactlyOneClaim := by
  intro V _ _ m cfg₁ cfg₂
  exact m.cipRSConfiguration_classification_exactly_one cfg₁ cfg₂

/-- Public claim: graph-level descriptor classifiers are sound for their returned relation. -/
def graphDescriptorClassifierSoundClaim : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration),
      m.GraphCipRSDescriptorClassificationHolds cfg₁ cfg₂
        (m.graphCipRSDescriptorClassifier cfg₁ cfg₂)

theorem graphDescriptorClassifierSoundClaim_holds :
    graphDescriptorClassifierSoundClaim := by
  intro V _ _ m cfg₁ cfg₂
  exact m.graphCipRSDescriptorClassifier_sound cfg₁ cfg₂

/-- Public refusal claim: graph descriptor classifiers refuse unresolved descriptor priorities. -/
def graphDescriptorClassifierRefusesUnresolvedClaim : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (cfg₁ cfg₂ : m.GraphConfiguration),
      ¬ m.GraphStereogenicByCIPDescriptor →
        m.graphCipRSDescriptorClassifier? cfg₁ cfg₂ = none

theorem graphDescriptorClassifierRefusesUnresolvedClaim_holds :
    graphDescriptorClassifierRefusesUnresolvedClaim := by
  intro V _ _ m cfg₁ cfg₂ h
  classical
  change
    (if _ : m.GraphStereogenicByCIPDescriptor then
      some (m.graphCipRSDescriptorClassifier cfg₁ cfg₂)
    else
      none) = none
  rw [dif_neg h]

/-- Public claim: non-tetrahedral descriptor profiles have involutive mirror semantics. -/
def stereoElementProfileMirrorInvolutiveClaim : Prop :=
  ∀ (V : Type*) (profile : StereoElementProfile V), profile.mirror.mirror = profile

theorem stereoElementProfileMirrorInvolutiveClaim_holds :
    stereoElementProfileMirrorInvolutiveClaim := by
  intro V profile
  exact StereoElementProfile.mirror_mirror profile

/-- Public claim: a mirror-changing conformational profile rules out ensemble achirality. -/
def conformationalProfileChiralRefutesAchiralClaim : Prop :=
  ∀ (V : Type*) (system : ConformationalStereoSystem V)
    (c : MolecularConformation V),
      system.ProfileChiralAt c → ¬ system.ensemble.AchiralWithin c

theorem conformationalProfileChiralRefutesAchiralClaim_holds :
    conformationalProfileChiralRefutesAchiralClaim := by
  intro V system c hprofile
  exact system.not_achiralWithin_of_profileChiral hprofile

/-- Public claim: descriptor-chiral ensembles are not descriptor-achiral ensembles. -/
def descriptorChiralEnsembleRefutesAchiralClaim : Prop :=
  ∀ (V : Type*) (system : ConformationalStereoSystem V),
      system.DescriptorChiralEnsemble → ¬ system.DescriptorAchiralEnsemble

theorem descriptorChiralEnsembleRefutesAchiralClaim_holds :
    descriptorChiralEnsembleRefutesAchiralClaim := by
  intro V system hchiral
  exact system.not_descriptorAchiralEnsemble_of_descriptorChiralEnsemble hchiral

end
end Engine
end TetraStereo
