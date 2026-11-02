import TetraStereo.Engine.HostAnalysisRequestBuilder
import TetraStereo.Examples.HostModuleCompiler
import TetraStereo.Examples.HostAnalysisRequestBuilderFixtures
import TetraStereo.Examples.HostAnalysisRequestKernelValidation
import TetraStereo.Examples.HostAnalysisRequestKernelCertificateCollision
import TetraStereo.Examples.HostAnalysisRequestKernelCompactName
import TetraStereo.Examples.HostAnalysisRequestKernelDetectorCoverage

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo
namespace Examples
namespace HostAnalysisRequestBuilder

open Engine
open OneCenter

noncomputable section











/-- The molecule-derived analysis request emits one official-stereo generated package. -/
theorem helicalBridgeMoleculeAnalysisRequest_official_count :
    helicalBridgeMoleculeAnalysisRequest.officialStereoRequests.length = 1 :=
  rfl

/-- The molecule-derived analysis request includes all seven broad theorem-family packages. -/
theorem helicalBridgeMoleculeAnalysisRequest_claim_count :
    helicalBridgeMoleculeAnalysisRequest.claimRequests.length = 7 :=
  rfl

/-- The derived generated suite manifest imports eight generated modules. -/
theorem helicalBridgeMoleculeAnalysisRequest_manifest_import_count :
    helicalBridgeMoleculeAnalysisRequest.suiteRequest.manifestImportModules.length = 8 :=
  rfl



theorem broadSurfaceAnalysisPlan_output_count :
    broadSurfaceAnalysisPlan.outputs.length = 17 :=
  rfl


theorem broadSurfaceMoleculeAnalysisRequest_detector_coverage :
    broadSurfaceMoleculeAnalysisRequest.detectorCoverage =
      { rawDoubleBonds := 3
        assignedDoubleBonds := 1
        cumulenes := 1
        axes := 1
        planes := 1
        helices := 1
        conformations := 1
        ensembles := 1
        auxiliaryRule5Nodes := 1
        phantomNodes := 1
        lonePairNodes := 1
        total := 13 } :=
  HostAnalysisRequestKernelProof.broadSurfaceMoleculeAnalysisRequest_detector_coverage

/-- Target-derived broad-claim dependencies are deduplicated in first-requested order. -/
theorem broadSurfaceAnalysisPlan_required_claim_targets :
    broadSurfaceAnalysisPlan.requiredClaimTargets =
      [ HostStereoClaimTarget.officialCIPAssignmentSuccessResolved
      , HostStereoClaimTarget.stereoElementProfileMirrorInvolutive
      , HostStereoClaimTarget.multiCenterCipRSClassificationExactlyOne
      , HostStereoClaimTarget.graphDescriptorClassifierSound
      , HostStereoClaimTarget.graphDescriptorClassifierRefusesUnresolved
      , HostStereoClaimTarget.conformationalProfileChiralRefutesAchiral
      , HostStereoClaimTarget.descriptorChiralEnsembleRefutesAchiral
      ] :=
  rfl


theorem broadSurfaceMoleculeAnalysisRequest_official_count :
    broadSurfaceMoleculeAnalysisRequest.officialStereoRequests.length = 1 :=
  rfl

/-- Molecule-derived official-stereo packages carry exact owner metadata for suite validation. -/
theorem broadSurfaceMoleculeAnalysisRequest_official_owner :
    (broadSurfaceMoleculeAnalysisRequest.officialStereoRequests.map fun request =>
      (request.ownerRequestKey, request.packageKeySuffix)) =
      [("host-analysis-broad-stereochemical-surface", "official-center-comparison")] :=
  rfl

/-- The broad analysis request derives all seven broad claim packages from target dependencies. -/
theorem broadSurfaceMoleculeAnalysisRequest_claim_count :
    broadSurfaceMoleculeAnalysisRequest.claimRequests.length = 7 :=
  rfl

/-- The broad analysis request derives sixteen source-bearing target witnesses. -/
theorem broadSurfaceMoleculeAnalysisRequest_witness_count :
    broadSurfaceMoleculeAnalysisRequest.witnessRequests.length = 16 :=
  rfl

/-- The broad analysis request derives stable request-scoped target-witness keys. -/
theorem broadSurfaceMoleculeAnalysisRequest_witness_keys :
    broadSurfaceMoleculeAnalysisRequest.witnessRequestKeys =
      [ "host-analysis-broad-stereochemical-surface::target-witness::axial::axial-unit::descriptor-result::axial-Ra::source::source-axial-a5-a7-a1-a2-a3-a4"
      , "host-analysis-broad-stereochemical-surface::target-witness::planar::planar-unit::descriptor-result::planar-Rp::source::source-planar-a1-a2-a3-a1-a2-a3"
      , "host-analysis-broad-stereochemical-surface::target-witness::helical::helical-unit::descriptor-result::helical-M::source::source-helical-a1-a0-a2-a1-a2"
      , "host-analysis-broad-stereochemical-surface::target-witness::alkene::alkene-unit::descriptor-result::alkene-Z::source::source-alkene-a8-a9"
      , "host-analysis-broad-stereochemical-surface::target-witness::cumulene::cumulene-unit"
      , "host-analysis-broad-stereochemical-surface::target-witness::auxiliary-rule5::auxiliary-rule5-node::descriptor-result::auxiliary-rule5-auxiliary-tetrahedral-center-senior::source::source-auxiliary-rule5-a1-a0-root-a0"
      , "host-analysis-broad-stereochemical-surface::target-witness::phantom::phantom-node"
      , "host-analysis-broad-stereochemical-surface::target-witness::lone-pair::lone-pair-node"
      , "host-analysis-broad-stereochemical-surface::target-witness::multi-center-graph-relation::multicenter-relation::graph-result::multi-center-exactly-one"
      , "host-analysis-broad-stereochemical-surface::target-witness::graph-classifier-sound::graph-classifier-sound::graph-result::descriptor-classifier-sound"
      , "host-analysis-broad-stereochemical-surface::target-witness::graph-classifier-sound::graph-classifier-self-same::graph-result::descriptor-classifier-sound::configuration::identity-self::outcome::same"
      , "host-analysis-broad-stereochemical-surface::target-witness::graph-classifier-sound::graph-classifier-mirror-meso-same::graph-result::descriptor-classifier-sound::configuration::identity-mirror::precondition::descriptor-meso-left::outcome::same"
      , "host-analysis-broad-stereochemical-surface::target-witness::graph-classifier-sound::graph-classifier-mirror-chiral-enantiomeric::graph-result::descriptor-classifier-sound::configuration::identity-mirror::precondition::descriptor-chiral-left::outcome::enantiomeric"
      , "host-analysis-broad-stereochemical-surface::target-witness::graph-classifier-refusal::graph-classifier-refusal::graph-result::descriptor-classifier-refusal"
      , "host-analysis-broad-stereochemical-surface::target-witness::conformer::conformer-profile-chiral::descriptor-result::conformer-kind-chiral::source::source-conformer-k-a0-a1-a2-a3-a4-a5-a6-a7-a8-a9-a10-a11"
      , "host-analysis-broad-stereochemical-surface::target-witness::ensemble::ensemble-descriptor-chiral::descriptor-result::ensemble-kind-chiral::source::source-ensemble-k-a0-a1-a2-a3-a4-a5-a6-a7-a8-a9-a10-a11"
      ] :=
  rfl

/-- Result-bound target certificates use descriptor-result public keys, not coverage-only keys. -/
theorem broadSurfaceMoleculeAnalysisRequest_first_certificate_key_result_bound :
    broadSurfaceMoleculeAnalysisRequest.witnessCertificateKeys.head? =
      some "host-analysis-broad-stereochemical-surface::target-witness::axial::axial-unit::descriptor-result::axial-Ra::source::source-axial-a5-a7-a1-a2-a3-a4::descriptor-result-certificate" :=
  rfl

/-- Every broad demo target witness has one theorem-family dependency. -/
theorem broadSurfaceMoleculeAnalysisRequest_witness_dependency_counts :
    (broadSurfaceMoleculeAnalysisRequest.witnessRequests.map fun request =>
      request.dependencyTheoremNames.length) =
      List.replicate 16 1 :=
  rfl

/-- The broad demo target witnesses reference the expected generated claim theorems. -/
theorem broadSurfaceMoleculeAnalysisRequest_witness_dependency_theorems :
    (broadSurfaceMoleculeAnalysisRequest.witnessRequests.map fun request =>
      request.dependencyTheoremNames) =
      (broadSurfaceMoleculeAnalysisRequest.witnessRequests.map fun request =>
        broadSurfaceMoleculeAnalysisRequest.claimTheoremsForKeys
          request.witness.theoremFamilyKeys) :=
  rfl

/-- Every generated target witness carries explicit non-vacuous coverage evidence. -/
theorem broadSurfaceMoleculeAnalysisRequest_witness_coverage_checked :
    (broadSurfaceMoleculeAnalysisRequest.witnessRequests.map fun request =>
      (request.witness.coverageChecked, request.witness.requiredCount)) =
      List.replicate 16 (true, 1) :=
  rfl

/-- Graph target witnesses recompute one detected tetrahedral center from the molecule source. -/
theorem broadSurfaceMoleculeAnalysisRequest_graph_witness_counts :
    (broadSurfaceMoleculeAnalysisRequest.witnessRequests.filterMap fun request =>
      if request.witness.kind = HostMoleculeTargetWitnessKind.graphRelation then
        some request.witness.observedCount
      else
        none) = [1, 1, 1, 1, 1, 1] :=
  rfl

/-- Graph target witnesses carry molecule-specialized theorem-family evidence, not just raw coverage. -/
theorem broadSurfaceMoleculeAnalysisRequest_graph_result_evidence :
    (broadSurfaceMoleculeAnalysisRequest.witnessRequests.filterMap fun request =>
      request.witness.graphResult?.map fun evidence =>
        (evidence.kind, evidence.sourceCenterCount, evidence.configurationPolicy,
          evidence.expectedOutcome?, evidence.outcomePrecondition, evidence.outcomeChecked,
          evidence.resultChecked)) =
      [ (HostMoleculeGraphResultEvidenceKind.multiCenterExactlyOne, 1,
          HostMoleculeGraphConfigurationPolicy.identityMirror, none,
          HostMoleculeGraphOutcomePrecondition.none, false, true)
      , (HostMoleculeGraphResultEvidenceKind.descriptorClassifierSound, 1,
          HostMoleculeGraphConfigurationPolicy.identityMirror, none,
          HostMoleculeGraphOutcomePrecondition.none, false, true)
      , (HostMoleculeGraphResultEvidenceKind.descriptorClassifierSound, 1,
          HostMoleculeGraphConfigurationPolicy.identitySelf, some CipRSClassRelation.same,
          HostMoleculeGraphOutcomePrecondition.none, true, true)
      , (HostMoleculeGraphResultEvidenceKind.descriptorClassifierSound, 1,
          HostMoleculeGraphConfigurationPolicy.identityMirror, some CipRSClassRelation.same,
          HostMoleculeGraphOutcomePrecondition.descriptorMesoLeft, true, true)
      , (HostMoleculeGraphResultEvidenceKind.descriptorClassifierSound, 1,
          HostMoleculeGraphConfigurationPolicy.identityMirror, some CipRSClassRelation.enantiomeric,
          HostMoleculeGraphOutcomePrecondition.descriptorChiralLeft, true, true)
      , (HostMoleculeGraphResultEvidenceKind.descriptorClassifierRefusal, 1,
          HostMoleculeGraphConfigurationPolicy.identityMirror, none,
          HostMoleculeGraphOutcomePrecondition.none, false, true)
      ] :=
  rfl

/-- The concrete graph outcome target emits an outcome-bound witness package. -/
def broadSurfaceConcreteGraphOutcomeWitnessRequest? : Option HostMoleculeTargetWitnessRequest :=
  match broadSurfaceMoleculeAnalysisRequest.witnessRequests.find? fun request =>
      request.witness.targetKeySuffix = "graph-classifier-self-same" with
  | some request => some request
  | none => none

/-- Concrete graph outcomes are encoded in public package keys, not hidden in prose. -/
theorem broadSurfaceConcreteGraphOutcomeWitnessRequest_key :
    broadSurfaceConcreteGraphOutcomeWitnessRequest?.map (fun request => request.key) =
      some
        "host-analysis-broad-stereochemical-surface::target-witness::graph-classifier-sound::graph-classifier-self-same::graph-result::descriptor-classifier-sound::configuration::identity-self::outcome::same" :=
  rfl

/-- The concrete graph outcome witness asks Lean to prove a self/same descriptor result. -/
theorem broadSurfaceConcreteGraphOutcomeWitnessRequest_evidence :
    broadSurfaceConcreteGraphOutcomeWitnessRequest?.map (fun request => request.witness.graphResult?) =
      some
        (some
          { kind := HostMoleculeGraphResultEvidenceKind.descriptorClassifierSound
            sourceCenterCount := 1
            requiredCenterCount := 1
            configurationPolicy := HostMoleculeGraphConfigurationPolicy.identitySelf
            expectedOutcome? := some CipRSClassRelation.same
            outcomePrecondition := HostMoleculeGraphOutcomePrecondition.none
            outcomeChecked := true
            resultChecked := true }) :=
  rfl

/-- Conditional mirror/same graph outcomes are represented as guarded graph certificates. -/
def broadSurfaceMirrorMesoGraphOutcomeWitnessRequest? : Option HostMoleculeTargetWitnessRequest :=
  match broadSurfaceMoleculeAnalysisRequest.witnessRequests.find? fun request =>
      request.witness.targetKeySuffix = "graph-classifier-mirror-meso-same" with
  | some request => some request
  | none => none

/-- The meso-guarded mirror/same target records its descriptor-meso precondition. -/
theorem broadSurfaceMirrorMesoGraphOutcomeWitnessRequest_evidence :
    broadSurfaceMirrorMesoGraphOutcomeWitnessRequest?.map
        (fun request => request.witness.graphResult?.map
          (fun evidence => (evidence.configurationPolicy, evidence.expectedOutcome?,
            evidence.outcomePrecondition, evidence.outcomeChecked))) =
      some
        (some
          (HostMoleculeGraphConfigurationPolicy.identityMirror, some CipRSClassRelation.same,
            HostMoleculeGraphOutcomePrecondition.descriptorMesoLeft, true)) :=
  rfl

/-- Conditional mirror/enantiomeric graph outcomes are represented as guarded graph certificates. -/
def broadSurfaceMirrorChiralGraphOutcomeWitnessRequest? : Option HostMoleculeTargetWitnessRequest :=
  match broadSurfaceMoleculeAnalysisRequest.witnessRequests.find? fun request =>
      request.witness.targetKeySuffix = "graph-classifier-mirror-chiral-enantiomeric" with
  | some request => some request
  | none => none

/-- The chiral-guarded mirror/enantiomeric target records its descriptor-chiral precondition. -/
theorem broadSurfaceMirrorChiralGraphOutcomeWitnessRequest_evidence :
    broadSurfaceMirrorChiralGraphOutcomeWitnessRequest?.map
        (fun request => request.witness.graphResult?.map
          (fun evidence => (evidence.configurationPolicy, evidence.expectedOutcome?,
            evidence.outcomePrecondition, evidence.outcomeChecked))) =
      some
        (some
          (HostMoleculeGraphConfigurationPolicy.identityMirror,
            some CipRSClassRelation.enantiomeric,
            HostMoleculeGraphOutcomePrecondition.descriptorChiralLeft, true)) :=
  rfl

/-- Concrete graph outcome requests using mirror configurations are refused before source writing. -/
def unsupportedMirrorConcreteGraphOutcomeRequest : HostMoleculeAnalysisRequest :=
  { broadSurfaceMoleculeAnalysisRequest with
    analysisPlan :=
      { outputs :=
          [ HostStereochemicalOutputTarget.officialCenterComparison
              broadSurfaceOfficialCenterTarget
          , HostStereochemicalOutputTarget.graphRelation
              { keySuffix := "unsupported-mirror-same"
                description := "unsupported mirror/same concrete graph outcome"
                kind := HostGraphRelationTargetKind.descriptorClassifierSound
                expectedOutcome? := some CipRSClassRelation.same } ] } }

/-- The public builder does not confuse mirror comparison targets with self/same certificates. -/
theorem unsupportedMirrorConcreteGraphOutcomeRequest_rejected :
    (match unsupportedMirrorConcreteGraphOutcomeRequest.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by rfl

/-- Concrete graph outcome requests using unsupported non-self outcomes are refused. -/
def unsupportedEnantiomericConcreteGraphOutcomeRequest : HostMoleculeAnalysisRequest :=
  { broadSurfaceMoleculeAnalysisRequest with
    analysisPlan :=
      { outputs :=
          [ HostStereochemicalOutputTarget.officialCenterComparison
              broadSurfaceOfficialCenterTarget
          , HostStereochemicalOutputTarget.graphRelation
              { keySuffix := "unsupported-self-enantiomeric"
                description := "unsupported self/enantiomeric concrete graph outcome"
                kind := HostGraphRelationTargetKind.descriptorClassifierSound
                configurationPolicy := HostMoleculeGraphConfigurationPolicy.identitySelf
                expectedOutcome? := some CipRSClassRelation.enantiomeric } ] } }

/-- The public builder refuses unsupported exact graph outcomes instead of generating bad proofs. -/
theorem unsupportedEnantiomericConcreteGraphOutcomeRequest_rejected :
    (match unsupportedEnantiomericConcreteGraphOutcomeRequest.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by rfl

/-- Guarded graph outcome preconditions are meaningless without a requested concrete outcome. -/
def unsupportedGuardedGraphTargetWithoutOutcome : HostGraphRelationTarget where
  keySuffix := "guarded-without-outcome"
  description := "guarded graph precondition without concrete outcome"
  kind := HostGraphRelationTargetKind.descriptorClassifierSound
  outcomePrecondition := HostMoleculeGraphOutcomePrecondition.descriptorMesoLeft

/-- Target validation catches preconditions that cannot generate a guarded theorem statement. -/
theorem unsupportedGuardedGraphTargetWithoutOutcome_rejected :
    (match unsupportedGuardedGraphTargetWithoutOutcome.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by rfl

/-- A forged concrete graph outcome witness whose outcome flag was not checked. -/
def forgedUncheckedConcreteGraphOutcomeWitness? : Option HostMoleculeTargetWitness :=
  broadSurfaceConcreteGraphOutcomeWitnessRequest?.map fun request =>
    { request.witness with
      graphResult? :=
        request.witness.graphResult?.map fun evidence =>
          { evidence with outcomeChecked := false } }

/-- Concrete graph outcome evidence must explicitly mark the outcome as checked. -/
theorem forgedUncheckedConcreteGraphOutcomeWitness_not_ready :
    forgedUncheckedConcreteGraphOutcomeWitness?.map (fun witness => witness.ready) = some false :=
  by rfl

/-- A forged concrete graph outcome witness asking for an unsupported relation. -/
def forgedUnsupportedConcreteGraphOutcomeWitness? : Option HostMoleculeTargetWitness :=
  broadSurfaceConcreteGraphOutcomeWitnessRequest?.map fun request =>
    { request.witness with
      graphResult? :=
        request.witness.graphResult?.map fun evidence =>
          { evidence with expectedOutcome? := some CipRSClassRelation.diastereomeric } }

/-- Concrete graph outcome evidence is checked against the compiler-supported proof policy. -/
theorem forgedUnsupportedConcreteGraphOutcomeWitness_not_ready :
    forgedUnsupportedConcreteGraphOutcomeWitness?.map (fun witness => witness.ready) = some false :=
  by rfl

/-- Seven broad demo targets are bound to exact descriptor/result values, not mere coverage. -/
theorem broadSurfaceMoleculeAnalysisRequest_descriptor_result_count :
    (broadSurfaceMoleculeAnalysisRequest.witnessRequests.filterMap fun request =>
      request.witness.descriptorResult?).length = 7 :=
  rfl

/-- Every result-bound broad demo target has one exact source match. -/
theorem broadSurfaceMoleculeAnalysisRequest_descriptor_result_matched_counts :
    (broadSurfaceMoleculeAnalysisRequest.witnessRequests.filterMap fun request =>
      request.witness.descriptorResult?.map fun evidence => evidence.matchedCount) =
      List.replicate 7 1 :=
  rfl

/-- Public certificates carry exact descriptor-result source counts where the target is result-bound. -/
theorem broadSurfaceMoleculeAnalysisRequest_certificate_descriptor_source_counts :
    (broadSurfaceMoleculeAnalysisRequest.witnessRequests.map fun request =>
      request.certificate.sourceDescriptorResultCount) =
      [1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1] :=
  rfl

/-- Public graph target certificates carry graph source counts where the target is graph-bound. -/
theorem broadSurfaceMoleculeAnalysisRequest_certificate_graph_source_counts :
    (broadSurfaceMoleculeAnalysisRequest.witnessRequests.map fun request =>
      request.certificate.sourceGraphResultCenterCount) =
      [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0] :=
  rfl

/-- Every generated target witness now exposes a public target-certificate object. -/
theorem broadSurfaceMoleculeAnalysisRequest_target_certificate_count :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.witnessCertificateDefinitionNames.length = 16 :=
  rfl

/-- The derived broad generated suite manifest imports twenty-four generated modules. -/
theorem broadSurfaceMoleculeAnalysisRequest_manifest_import_count :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.manifestImportModules.length = 24 :=
  rfl

/-- The broad request passes all executable host-boundary validation checks. -/
theorem broadSurfaceMoleculeAnalysisRequest_validate :
    (match broadSurfaceMoleculeAnalysisRequest.validateGeneratedShape with
      | Except.ok () => true
      | Except.error _ => false) = true :=
  by
    rw [HostAnalysisRequestKernelProof.broadSurface_request_valid]

/-- Reassociation lets a known failing executable check reject an arbitrary preceding validation
prefix without evaluating that prefix in the kernel. -/
private theorem validation_rejected_after_error (pre : Except String Unit) (message : String) :
    (match (pre >>= fun _ => Except.error message) with
      | Except.ok () => false
      | Except.error _ => true) = true := by
  cases pre <;> rfl

/-- Appending a value already present in a list creates an executable duplicate. -/
private theorem duplicate_strings_after_appending_present {x : String} {xs : List String}
    (h : x ∈ xs) : hasDuplicateStrings (xs ++ [x]) = true := by
  induction xs with
  | nil => simp at h
  | cons a rest ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · simp [hasDuplicateStrings]
      · simp [hasDuplicateStrings, ih h]

/-- A value followed later by the same value creates an executable duplicate, independently of
the prefix preceding its first occurrence. -/
private theorem duplicate_strings_of_mem_suffix {x : String} {xs suffix : List String}
    (h : x ∈ suffix) : hasDuplicateStrings (xs ++ x :: suffix) = true := by
  induction xs with
  | nil => simp [hasDuplicateStrings, h]
  | cons a rest ih => simp [hasDuplicateStrings, ih]

/-- A structural error witness lets later proofs compose validation phases without evaluating
unrelated successful prefixes. -/
private def validationFailed (result : Except String Unit) : Prop :=
  ∃ message, result = Except.error message

private theorem validation_failed_before
    (pre result : Except String Unit) (h : validationFailed result) :
    validationFailed (do pre; result) := by
  rcases h with ⟨message, hresult⟩
  cases pre with
  | error earlier => exact ⟨earlier, rfl⟩
  | ok _ => exact ⟨message, hresult⟩

private theorem validation_failed_after
    (result post : Except String Unit) (h : validationFailed result) :
    validationFailed (do result; post) := by
  rcases h with ⟨message, hresult⟩
  rw [hresult]
  exact ⟨message, rfl⟩

private theorem validation_failed_around
    (pre result post : Except String Unit) (h : validationFailed result) :
    validationFailed (do pre; result; post) :=
  validation_failed_before pre (do result; post) (validation_failed_after result post h)

/-- Lift a failing singleton witness validation through the enclosing suite phases. -/
private theorem validation_failed_of_single_witness
    (request : HostAnalysisSuiteRequest) (witnessRequest : HostMoleculeTargetWitnessRequest)
    (hrequests : request.witnessRequests = [witnessRequest])
    (hwitness : validationFailed (request.validateWitnessRequestShape witnessRequest)) :
    validationFailed request.validateGeneratedShape := by
  have hwitnesses : validationFailed request.validateWitnessRequestShapes := by
    unfold HostAnalysisSuiteRequest.validateWitnessRequestShapes
    rw [hrequests]
    unfold HostAnalysisSuiteRequest.validateWitnessRequestList
    exact validation_failed_after _ _ hwitness
  unfold HostAnalysisSuiteRequest.validateGeneratedShape
  apply validation_failed_before
  apply validation_failed_before
  apply validation_failed_before
  apply validation_failed_after
  exact hwitnesses

/-! ### Target-witness hardening regression checks -/

/-- Generated identifiers reject Lean command keywords, not just unsafe characters. -/
theorem generatedIdentifier_export_keyword_rejected :
    leanIdentifierSegment? "export" = false :=
  by rfl

/-- Generated identifiers reject tactic/control keywords that Lean refuses as declarations. -/
theorem generatedIdentifier_return_keyword_rejected :
    leanIdentifierSegment? "return" = false :=
  by rfl

/-- Generated identifiers reject namespace-scoping keywords that Lean refuses as declarations. -/
theorem generatedIdentifier_include_keyword_rejected :
    leanIdentifierSegment? "include" = false :=
  by rfl

/-- Generated witness namespace segments cannot reuse Lean reserved words. -/
def keywordWitnessNamespaceAnalysisRequest : HostMoleculeAnalysisRequest :=
  { broadSurfaceMoleculeAnalysisRequest with
    witnessNamespacePath := ["namespace"] }

/-- Reserved Lean keywords in generated witness namespaces are rejected before source writing. -/
theorem keywordWitnessNamespaceAnalysisRequest_rejected :
    (match keywordWitnessNamespaceAnalysisRequest.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by rfl

/-- A forged witness cannot bypass coverage by setting `coverageChecked := false`. -/
def forgedUncheckedTargetWitnessRequest : HostMoleculeTargetWitnessRequest where
  key := "forged-analysis::target-witness::axial::forged-target"
  description := "forged unchecked target witness"
  witness :=
    { requestKey := "forged-analysis"
      targetKeySuffix := "forged-target"
      targetDescription := "forged target"
      targetLabel := "axial descriptor"
      kind := HostMoleculeTargetWitnessKind.noncenterDescriptor
      coverageField := HostMoleculeTargetCoverageField.axial
      observedCount := 0
      requiredCount := 1
      coverageChecked := false
      theoremFamilyKeys := ["forged-analysis::host-claim-stereo-element-mirror"] }
  fileName := "HostMoleculeTargetWitness_kforged_x45_analysis_kaxial_kforged_x45_target.lean"
  namespacePath := ["TetraStereoGenerated", "Examples", "ForgedWitnesses"]
  definitionName := "hostMoleculeTargetWitness_kforged_x45_analysis_kaxial_kforged_x45_target"
  theoremName := "host_molecule_target_witness_kforged_x45_analysis_kaxial_kforged_x45_target_checked"
  coverageSourceModule :=
    "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter"
  coverageSourcePacketName :=
    "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterPacket"
  coverageSourceAnnotationsName :=
    "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterBlueprint.annotations"
  coverageSourceBlueprintName :=
    "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterBlueprint"
  coverageSourceOwnerName :=
    "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.hostOfficialStereoOwnerRequestKey"
  coverageTheoremName := "host_molecule_target_witness_kforged_x45_analysis_kaxial_kforged_x45_target_coverage"
  dependencyTheoremNames :=
    ["TetraStereo.Engine.stereoElementProfileMirrorInvolutiveClaim_holds"]

/-- Coverage-bypass target witnesses fail executable package-shape validation. -/
theorem forgedUncheckedTargetWitnessRequest_rejected :
    (match forgedUncheckedTargetWitnessRequest.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by
    have hwitness : forgedUncheckedTargetWitnessRequest.witness.ready = false := by
      rfl
    have hreadiness : validationFailed
        forgedUncheckedTargetWitnessRequest.validateReadinessShape := by
      refine ⟨"host molecule target witness does not satisfy executable readiness checks", ?_⟩
      unfold HostMoleculeTargetWitnessRequest.validateReadinessShape
      rw [hwitness]
      rfl
    have hfailed : validationFailed forgedUncheckedTargetWitnessRequest.validateGeneratedShape := by
      unfold HostMoleculeTargetWitnessRequest.validateGeneratedShape
      apply validation_failed_before
      apply validation_failed_before
      exact hreadiness
    rcases hfailed with ⟨message, hresult⟩
    rw [hresult]

/-- A representative generated target witness for declaration-collision checks. -/
def broadSurfaceFirstTargetWitnessRequest : HostMoleculeTargetWitnessRequest :=
  match broadSurfaceMoleculeAnalysisRequest.witnessRequests with
  | request :: _ => request
  | [] => forgedUncheckedTargetWitnessRequest

private theorem broadSurfaceFirstTargetWitnessRequest_mem :
    broadSurfaceFirstTargetWitnessRequest ∈ broadSurfaceMoleculeAnalysisRequest.witnessRequests := by
  unfold broadSurfaceFirstTargetWitnessRequest
  cases h : broadSurfaceMoleculeAnalysisRequest.witnessRequests with
  | nil =>
      have hc := broadSurfaceMoleculeAnalysisRequest_witness_count
      rw [h] at hc
      contradiction
  | cons first rest => simp

/-- A suite manifest cannot reuse a generated witness coverage theorem declaration. -/
def witnessCoverageTheoremCollisionAnalysisRequest : HostMoleculeAnalysisRequest :=
  { broadSurfaceMoleculeAnalysisRequest with
    suiteNamespacePath := broadSurfaceMoleculeAnalysisRequest.witnessNamespacePath
    suiteTheoremName := broadSurfaceFirstTargetWitnessRequest.coverageTheoremName }

private theorem witnessCoverageCollision_manifest_mem :
    witnessCoverageTheoremCollisionAnalysisRequest.suiteRequest.manifestTheoremFullName ∈
      witnessCoverageTheoremCollisionAnalysisRequest.suiteRequest.witnessDeclarationNames := by
  rw [HostAnalysisSuiteRequest.witnessDeclarationNames, List.mem_flatMap]
  refine ⟨broadSurfaceFirstTargetWitnessRequest, broadSurfaceFirstTargetWitnessRequest_mem, ?_⟩
  unfold HostMoleculeTargetWitnessRequest.declarationNames
  have hm :
      witnessCoverageTheoremCollisionAnalysisRequest.suiteRequest.manifestTheoremFullName =
        leanQualifiedName broadSurfaceFirstTargetWitnessRequest.namespacePath
          broadSurfaceFirstTargetWitnessRequest.coverageTheoremName := by
    rfl
  rw [hm]
  simp

/-- Witness coverage theorem declarations participate in suite collision checks. -/
theorem witnessCoverageTheoremCollisionAnalysisRequest_rejected :
    (match witnessCoverageTheoremCollisionAnalysisRequest.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by
    have hdup : hasDuplicateStrings
        witnessCoverageTheoremCollisionAnalysisRequest.suiteRequest.suiteDeclarationNames = true := by
      unfold HostAnalysisSuiteRequest.suiteDeclarationNames
      apply duplicate_strings_after_appending_present
      apply List.mem_append_right
      exact witnessCoverageCollision_manifest_mem
    have hunique : validationFailed
        witnessCoverageTheoremCollisionAnalysisRequest.suiteRequest.validateUniqueSuiteDeclarationNames := by
      refine ⟨"host analysis suite contains duplicate generated declaration names", ?_⟩
      unfold HostAnalysisSuiteRequest.validateUniqueSuiteDeclarationNames
      rw [hdup]
      rfl
    have hglobalDeclaration : validationFailed
        witnessCoverageTheoremCollisionAnalysisRequest.suiteRequest.validateGlobalDeclarationNameShape := by
      unfold HostAnalysisSuiteRequest.validateGlobalDeclarationNameShape
      exact validation_failed_after _ _ hunique
    have hglobal : validationFailed
        witnessCoverageTheoremCollisionAnalysisRequest.suiteRequest.validateGlobalNameShape := by
      unfold HostAnalysisSuiteRequest.validateGlobalNameShape
      exact validation_failed_around _ _ _ hglobalDeclaration
    have hsuite : validationFailed
        witnessCoverageTheoremCollisionAnalysisRequest.suiteRequest.validateGeneratedShape := by
      unfold HostAnalysisSuiteRequest.validateGeneratedShape
      apply validation_failed_before
      apply validation_failed_before
      apply validation_failed_before
      apply validation_failed_before
      exact hglobal
    have hanalysis : validationFailed
        witnessCoverageTheoremCollisionAnalysisRequest.validateGeneratedShape := by
      unfold HostMoleculeAnalysisRequest.validateGeneratedShape
      exact validation_failed_before _ _ hsuite
    rcases hanalysis with ⟨message, hresult⟩
    rw [hresult]

/-- A suite manifest cannot reuse a generated public target-certificate theorem declaration. -/
def witnessCertificateTheoremCollisionAnalysisRequest : HostMoleculeAnalysisRequest :=
  { broadSurfaceMoleculeAnalysisRequest with
    suiteNamespacePath := broadSurfaceMoleculeAnalysisRequest.witnessNamespacePath
    suiteTheoremName := broadSurfaceFirstTargetWitnessRequest.certificateTheoremName }

private theorem witnessCertificateCollision_manifest_mem :
    witnessCertificateTheoremCollisionAnalysisRequest.suiteRequest.manifestTheoremFullName ∈
      witnessCertificateTheoremCollisionAnalysisRequest.suiteRequest.witnessDeclarationNames := by
  rw [HostAnalysisSuiteRequest.witnessDeclarationNames, List.mem_flatMap]
  refine ⟨broadSurfaceFirstTargetWitnessRequest, broadSurfaceFirstTargetWitnessRequest_mem, ?_⟩
  unfold HostMoleculeTargetWitnessRequest.declarationNames
  have hm :
      witnessCertificateTheoremCollisionAnalysisRequest.suiteRequest.manifestTheoremFullName =
        broadSurfaceFirstTargetWitnessRequest.certificateTheoremFullName := by
    rfl
  rw [hm]
  simp

/-- Public target-certificate theorem declarations participate in suite collision checks. -/
theorem witnessCertificateTheoremCollisionAnalysisRequest_rejected :
    (match witnessCertificateTheoremCollisionAnalysisRequest.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by
    have hdup : hasDuplicateStrings
        witnessCertificateTheoremCollisionAnalysisRequest.suiteRequest.suiteDeclarationNames = true := by
      unfold HostAnalysisSuiteRequest.suiteDeclarationNames
      apply duplicate_strings_after_appending_present
      apply List.mem_append_right
      exact witnessCertificateCollision_manifest_mem
    have hunique : validationFailed
        witnessCertificateTheoremCollisionAnalysisRequest.suiteRequest.validateUniqueSuiteDeclarationNames := by
      refine ⟨"host analysis suite contains duplicate generated declaration names", ?_⟩
      unfold HostAnalysisSuiteRequest.validateUniqueSuiteDeclarationNames
      rw [hdup]
      rfl
    have hglobalDeclaration : validationFailed
        witnessCertificateTheoremCollisionAnalysisRequest.suiteRequest.validateGlobalDeclarationNameShape := by
      unfold HostAnalysisSuiteRequest.validateGlobalDeclarationNameShape
      exact validation_failed_after _ _ hunique
    have hglobal : validationFailed
        witnessCertificateTheoremCollisionAnalysisRequest.suiteRequest.validateGlobalNameShape := by
      unfold HostAnalysisSuiteRequest.validateGlobalNameShape
      exact validation_failed_around _ _ _ hglobalDeclaration
    have hsuite : validationFailed
        witnessCertificateTheoremCollisionAnalysisRequest.suiteRequest.validateGeneratedShape := by
      unfold HostAnalysisSuiteRequest.validateGeneratedShape
      apply validation_failed_before
      apply validation_failed_before
      apply validation_failed_before
      apply validation_failed_before
      exact hglobal
    have hanalysis : validationFailed
        witnessCertificateTheoremCollisionAnalysisRequest.validateGeneratedShape := by
      unfold HostMoleculeAnalysisRequest.validateGeneratedShape
      exact validation_failed_before _ _ hsuite
    rcases hanalysis with ⟨message, hresult⟩
    rw [hresult]

/-- A representative graph-result target witness from the broad demo request. -/
def broadSurfaceGraphSoundWitnessRequest : HostMoleculeTargetWitnessRequest :=
  HostAnalysisRequestKernelProof.witness9

/-- Standalone witness validation rejects mixed packet/annotation/blueprint provenance. -/
def forgedMixedGraphSourceWitnessRequest : HostMoleculeTargetWitnessRequest :=
  { broadSurfaceGraphSoundWitnessRequest with
    coverageSourcePacketName := "Foreign.Owner.packet"
    coverageSourceAnnotationsName := "Another.Owner.annotations"
    coverageSourceBlueprintName := "Third.Owner.blueprint" }

/-- Packet, annotation, and blueprint declarations must belong to the declared source module. -/
theorem forgedMixedGraphSourceWitnessRequest_rejected :
    (match forgedMixedGraphSourceWitnessRequest.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by
    have hsource : forgedMixedGraphSourceWitnessRequest.certificate.coverageSourceNamesReady =
        false := by
      rfl
    have hcertificate : forgedMixedGraphSourceWitnessRequest.certificate.ready = false := by
      unfold HostMoleculeTargetCertificate.ready
      rw [hsource]
      rfl
    have hwitness : forgedMixedGraphSourceWitnessRequest.witness.ready = true := by
      rfl
    have hreadiness : validationFailed
        forgedMixedGraphSourceWitnessRequest.validateReadinessShape := by
      refine ⟨"host molecule target certificate does not satisfy executable readiness checks", ?_⟩
      unfold HostMoleculeTargetWitnessRequest.validateReadinessShape
      rw [hwitness, hcertificate]
      rfl
    have hfailed : validationFailed forgedMixedGraphSourceWitnessRequest.validateGeneratedShape := by
      unfold HostMoleculeTargetWitnessRequest.validateGeneratedShape
      apply validation_failed_before
      apply validation_failed_before
      exact hreadiness
    rcases hfailed with ⟨message, hresult⟩
    rw [hresult]

/-- Public certificate readiness rejects mixed source-module provenance even outside a suite. -/
def forgedMixedGraphSourceCertificate : HostMoleculeTargetCertificate :=
  { broadSurfaceGraphSoundWitnessRequest.certificate with
    coverageSourcePacketName := "Foreign.Owner.packet"
    coverageSourceAnnotationsName := "Another.Owner.annotations"
    coverageSourceBlueprintName := "Third.Owner.blueprint" }

/-- Direct certificate consumers cannot accept foreign source expressions as ready. -/
theorem forgedMixedGraphSourceCertificate_not_ready :
    forgedMixedGraphSourceCertificate.ready = false :=
  by rfl

/-- Graph witnesses cannot carry two contradictory minimum-center requirements. -/
def forgedGraphRequiredCountMismatchWitness : HostMoleculeTargetWitness :=
  { broadSurfaceGraphSoundWitnessRequest.witness with
    observedCount := 2
    requiredCount := 1
    graphResult? :=
      broadSurfaceGraphSoundWitnessRequest.witness.graphResult?.map fun evidence =>
        { evidence with sourceCenterCount := 2, requiredCenterCount := 2 } }

/-- The graph evidence minimum must agree with the public witness minimum. -/
theorem forgedGraphRequiredCountMismatchWitness_not_ready :
    forgedGraphRequiredCountMismatchWitness.ready = false :=
  by rfl

/-- Generated name suffixes use escaped exact keys rather than colliding checksums. -/
theorem compactGeneratedNameSegment_collision_regression :
    compactGeneratedNameSegment "Tgt" "tpNAJeBnD0" ≠
      compactGeneratedNameSegment "Tgt" "MM3V5Gg1s5" :=
  HostAnalysisRequestKernelProof.compactGeneratedNameSegment_collision_regression

/-- A graph witness whose internal count and graph evidence agree with each other but not the source. -/
def forgedGraphSourceCountWitnessRequest : HostMoleculeTargetWitnessRequest :=
  let forgedWitness :=
    { broadSurfaceGraphSoundWitnessRequest.witness with
      observedCount := broadSurfaceGraphSoundWitnessRequest.witness.observedCount + 1
      graphResult? :=
        broadSurfaceGraphSoundWitnessRequest.witness.graphResult?.map fun evidence =>
          { evidence with sourceCenterCount := evidence.sourceCenterCount + 1 } }
  { broadSurfaceGraphSoundWitnessRequest with witness := forgedWitness }

/-- Suite validation recomputes graph-result counts from the source module, not witness literals. -/
def forgedGraphSourceCountSuite : HostAnalysisSuiteRequest :=
  { broadSurfaceMoleculeAnalysisRequest.suiteRequest with
    witnessRequests := [forgedGraphSourceCountWitnessRequest] }

/-- The sole official source request included in the broad generated suite. -/
private def broadSurfaceOfficialSourceRequest : HostOfficialStereoRequest :=
  (((forgedGraphSourceCountSuite.officialStereoRequests)[0]?).get (by rfl))

/-- Graph-result count forgeries are rejected before generated source is written. -/
theorem forgedGraphSourceCountSuite_rejected :
    (match forgedGraphSourceCountSuite.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by
    have hgraph : validationFailed
        (forgedGraphSourceCountSuite.validateWitnessGraphResultShape
          forgedGraphSourceCountWitnessRequest broadSurfaceOfficialSourceRequest) := by
      refine ⟨"host analysis suite graph target witness count does not match source host module", ?_⟩
      unfold HostAnalysisSuiteRequest.validateWitnessGraphResultShape
      simp only [show forgedGraphSourceCountWitnessRequest.witness.coverageField.requiresGraphResult =
        true by rfl, if_true]
      exact show requireHostRequestShape
            (forgedGraphSourceCountWitnessRequest.witness.observedCount =
              HostMoleculeGraphResult.detectedTetrahedralCenterCount
                broadSurfaceOfficialSourceRequest.packet)
            "host analysis suite graph target witness count does not match source host module" =
          .error "host analysis suite graph target witness count does not match source host module" by rfl
    have hcoverage : validationFailed
        (forgedGraphSourceCountSuite.validateWitnessCoverageSourceShape
          forgedGraphSourceCountWitnessRequest broadSurfaceOfficialSourceRequest) := by
      unfold HostAnalysisSuiteRequest.validateWitnessCoverageSourceShape
      apply validation_failed_before
      apply validation_failed_before
      apply validation_failed_before
      apply validation_failed_before
      apply validation_failed_before
      apply validation_failed_before
      exact hgraph
    have hwitness : validationFailed
        (forgedGraphSourceCountSuite.validateWitnessRequestShape
          forgedGraphSourceCountWitnessRequest) := by
      unfold HostAnalysisSuiteRequest.validateWitnessRequestShape
      rw [show forgedGraphSourceCountSuite.officialRequestByModule?
          forgedGraphSourceCountWitnessRequest.coverageSourceModule =
        some broadSurfaceOfficialSourceRequest by rfl]
      apply validation_failed_before
      apply validation_failed_before
      apply validation_failed_before
      apply validation_failed_after
      exact hcoverage
    have hwitnesses : validationFailed
        forgedGraphSourceCountSuite.validateWitnessRequestShapes := by
      unfold HostAnalysisSuiteRequest.validateWitnessRequestShapes
      unfold HostAnalysisSuiteRequest.validateWitnessRequestList
      exact validation_failed_after _ _ hwitness
    have hsuite : validationFailed forgedGraphSourceCountSuite.validateGeneratedShape := by
      unfold HostAnalysisSuiteRequest.validateGeneratedShape
      apply validation_failed_before
      apply validation_failed_before
      apply validation_failed_before
      apply validation_failed_after
      exact hwitnesses
    rcases hsuite with ⟨message, hresult⟩
    rw [hresult]

/-- A graph-source pseudo-center with one double bond is not accepted as tetrahedral evidence. -/
def multipleBondPseudoTetrahedralRaw : RawMolecule where
  atoms := List.replicate 5 (AtomSpec.aliphatic Element.C)
  bonds :=
    [ { source := 0, target := 1, kind := ParsedBondKind.double }
    , { source := 0, target := 2, kind := ParsedBondKind.single }
    , { source := 0, target := 3, kind := ParsedBondKind.single }
    , { source := 0, target := 4, kind := ParsedBondKind.single } ]

/-- Multiple-bond pseudo-centers are rejected by graph-source detection. -/
theorem multipleBondPseudoTetrahedralRaw_detected_center_count :
    HostMoleculeGraphResult.detectedTetrahedralCenterCount
      (rawMoleculePacket multipleBondPseudoTetrahedralRaw) = 0 :=
  by rfl

/-- A ready-looking witness with a fake theorem-family package key. -/
def forgedMissingDependencyTargetWitnessRequest : HostMoleculeTargetWitnessRequest where
  key := "forged-analysis::target-witness::axial::forged-target"
  description := "forged missing-dependency target witness"
  witness :=
    { requestKey := "forged-analysis"
      targetKeySuffix := "forged-target"
      targetDescription := "forged target"
      targetLabel := "axial descriptor"
      kind := HostMoleculeTargetWitnessKind.noncenterDescriptor
      coverageField := HostMoleculeTargetCoverageField.axial
      observedCount := 1
      requiredCount := 1
      coverageChecked := true
      theoremFamilyKeys := ["forged-analysis::missing-claim-package"] }
  fileName := "HostMoleculeTargetWitness_kforged_x45_analysis_kaxial_kforged_x45_target.lean"
  namespacePath := ["TetraStereoGenerated", "Examples", "ForgedWitnesses"]
  definitionName := "hostMoleculeTargetWitness_kforged_x45_analysis_kaxial_kforged_x45_target"
  theoremName := "host_molecule_target_witness_kforged_x45_analysis_kaxial_kforged_x45_target_checked"
  coverageSourceModule :=
    "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter"
  coverageSourcePacketName :=
    "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterPacket"
  coverageSourceAnnotationsName :=
    "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterBlueprint.annotations"
  coverageSourceBlueprintName :=
    "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterBlueprint"
  coverageSourceOwnerName :=
    "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.hostOfficialStereoOwnerRequestKey"
  coverageTheoremName := "host_molecule_target_witness_kforged_x45_analysis_kaxial_kforged_x45_target_coverage"
  dependencyTheoremNames :=
    ["TetraStereo.Engine.stereoElementProfileMirrorInvolutiveClaim_holds"]

/-- A suite rejects witnesses whose theorem-family keys are absent from included claim packages. -/
def forgedMissingDependencyTargetWitnessSuite : HostAnalysisSuiteRequest where
  key := "forged-analysis"
  description := "forged missing-dependency target witness suite"
  officialStereoRequests := broadSurfaceMoleculeAnalysisRequest.officialStereoRequests
  witnessRequests := [forgedMissingDependencyTargetWitnessRequest]

/-- Fake theorem-family keys are rejected at the suite boundary. -/
theorem forgedMissingDependencyTargetWitnessSuite_rejected :
    (match forgedMissingDependencyTargetWitnessSuite.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by
    have hdependency : validationFailed
        (forgedMissingDependencyTargetWitnessSuite.validateWitnessDependencyShape
          forgedMissingDependencyTargetWitnessRequest) := by
      refine ⟨"host analysis suite contains target witness dependency keys absent from claim packages", ?_⟩
      unfold HostAnalysisSuiteRequest.validateWitnessDependencyShape
      rfl
    have hwitness : validationFailed
        (forgedMissingDependencyTargetWitnessSuite.validateWitnessRequestShape
          forgedMissingDependencyTargetWitnessRequest) := by
      unfold HostAnalysisSuiteRequest.validateWitnessRequestShape
      rw [show forgedMissingDependencyTargetWitnessSuite.officialRequestByModule?
          forgedMissingDependencyTargetWitnessRequest.coverageSourceModule =
        some broadSurfaceOfficialSourceRequest by rfl]
      apply validation_failed_before
      apply validation_failed_before
      apply validation_failed_before
      apply validation_failed_before
      exact hdependency
    have hsuite := validation_failed_of_single_witness
      forgedMissingDependencyTargetWitnessSuite forgedMissingDependencyTargetWitnessRequest
      (by rfl) hwitness
    rcases hsuite with ⟨message, hresult⟩
    rw [hresult]

/-- An unreferenced claim package cannot use another suite owner's package key. -/
def forgedUnreferencedForeignClaimRequest : HostStereoClaimRequest where
  target := HostStereoClaimTarget.graphDescriptorClassifierSound
  key := "foreign-analysis::host-claim-graph-classification"
  description := "forged unreferenced foreign claim"
  namespacePath := ["TetraStereoGenerated", "Examples", "ForgedForeignClaims"]

/-- A suite carrying only an unscoped foreign claim package is malformed. -/
def forgedUnreferencedForeignClaimSuite : HostAnalysisSuiteRequest where
  key := "forged-analysis"
  description := "forged unreferenced foreign claim suite"
  claimRequests := [forgedUnreferencedForeignClaimRequest]

/-- Claim package keys are scoped even when no target witness references the claim. -/
theorem forgedUnreferencedForeignClaimSuite_rejected :
    (match forgedUnreferencedForeignClaimSuite.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by rfl

/-- A wrong theorem family can try to masquerade under the expected target-witness key. -/
def forgedWrongTargetClaimRequest : HostStereoClaimRequest where
  target := HostStereoClaimTarget.graphDescriptorClassifierSound
  key := "forged-analysis::host-claim-stereo-element-mirror"
  description := "forged wrong-target claim"
  namespacePath := ["TetraStereoGenerated", "Examples", "ForgedClaims"]

/-- A witness whose dependency key is present but attached to the wrong claim target. -/
def forgedWrongTargetDependencyWitnessRequest : HostMoleculeTargetWitnessRequest where
  key := "forged-analysis::target-witness::axial::forged-target"
  description := "forged wrong-target dependency witness"
  witness :=
    { requestKey := "forged-analysis"
      targetKeySuffix := "forged-target"
      targetDescription := "forged target"
      targetLabel := "axial descriptor"
      kind := HostMoleculeTargetWitnessKind.noncenterDescriptor
      coverageField := HostMoleculeTargetCoverageField.axial
      observedCount := 1
      requiredCount := 1
      coverageChecked := true
      theoremFamilyKeys := ["forged-analysis::host-claim-stereo-element-mirror"] }
  fileName := "HostMoleculeTargetWitness_kforged_x45_analysis_kaxial_kforged_x45_target.lean"
  namespacePath := ["TetraStereoGenerated", "Examples", "ForgedWitnesses"]
  definitionName := "hostMoleculeTargetWitness_kforged_x45_analysis_kaxial_kforged_x45_target"
  theoremName := "host_molecule_target_witness_kforged_x45_analysis_kaxial_kforged_x45_target_checked"
  coverageSourceModule :=
    "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter"
  coverageSourcePacketName :=
    "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterPacket"
  coverageSourceAnnotationsName :=
    "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterBlueprint.annotations"
  coverageSourceBlueprintName :=
    "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterBlueprint"
  coverageSourceOwnerName :=
    "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.hostOfficialStereoOwnerRequestKey"
  coverageTheoremName := "host_molecule_target_witness_kforged_x45_analysis_kaxial_kforged_x45_target_coverage"
  dependencyTheoremNames :=
    ["TetraStereoGenerated.Examples.ForgedClaims.host_graph_descriptor_classifier_sound"]
  imports :=
    [ "TetraStereo.Engine.HostAnalysisRequestBuilder"
    , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter"
    , "TetraStereoGenerated.Examples.ForgedClaims.HostGraphClassificationSoundClaim" ]

/-- Present dependency keys are rejected if they are not canonical for their actual claim target. -/
def forgedWrongTargetDependencySuite : HostAnalysisSuiteRequest where
  key := "forged-analysis"
  description := "forged wrong-target dependency suite"
  officialStereoRequests := broadSurfaceMoleculeAnalysisRequest.officialStereoRequests
  claimRequests := [forgedWrongTargetClaimRequest]
  witnessRequests := [forgedWrongTargetDependencyWitnessRequest]

/-- Wrong theorem-family targets cannot authenticate by reusing a plausible package key. -/
theorem forgedWrongTargetDependencySuite_rejected :
    (match forgedWrongTargetDependencySuite.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by
    have hkey : validationFailed
        (forgedWrongTargetDependencySuite.validateWitnessClaimKeyShape
          "forged-analysis::host-claim-stereo-element-mirror") := by
      refine ⟨"host analysis suite target witness dependency key is not canonical for its claim target", ?_⟩
      unfold HostAnalysisSuiteRequest.validateWitnessClaimKeyShape
      rfl
    have hkeys : validationFailed
        (forgedWrongTargetDependencySuite.validateWitnessClaimKeyList
          forgedWrongTargetDependencyWitnessRequest.witness.theoremFamilyKeys) := by
      unfold HostAnalysisSuiteRequest.validateWitnessClaimKeyList
      exact validation_failed_after _ _ hkey
    have hdependency : validationFailed
        (forgedWrongTargetDependencySuite.validateWitnessDependencyShape
          forgedWrongTargetDependencyWitnessRequest) := by
      unfold HostAnalysisSuiteRequest.validateWitnessDependencyShape
      apply validation_failed_before
      apply validation_failed_after
      exact hkeys
    have hwitness : validationFailed
        (forgedWrongTargetDependencySuite.validateWitnessRequestShape
          forgedWrongTargetDependencyWitnessRequest) := by
      unfold HostAnalysisSuiteRequest.validateWitnessRequestShape
      rw [show forgedWrongTargetDependencySuite.officialRequestByModule?
          forgedWrongTargetDependencyWitnessRequest.coverageSourceModule =
        some broadSurfaceOfficialSourceRequest by rfl]
      apply validation_failed_before
      apply validation_failed_before
      apply validation_failed_before
      apply validation_failed_before
      exact hdependency
    have hsuite := validation_failed_of_single_witness
      forgedWrongTargetDependencySuite forgedWrongTargetDependencyWitnessRequest
      (by rfl) hwitness
    rcases hsuite with ⟨message, hresult⟩
    rw [hresult]

/-- A correct claim package under a forged request key. -/
def forgedCrossRequestSourceClaimRequest : HostStereoClaimRequest where
  target := HostStereoClaimTarget.stereoElementProfileMirrorInvolutive
  key := "forged-analysis::host-claim-stereo-element-mirror"
  description := "forged same-target claim for cross-request source"
  namespacePath := ["TetraStereoGenerated", "Examples", "ForgedCrossRequestClaims"]

/-- A witness whose own key is scoped correctly but whose source module came from another request. -/
def forgedCrossRequestSourceWitnessRequest : HostMoleculeTargetWitnessRequest where
  key := "forged-analysis::target-witness::axial::forged-target"
  description := "forged cross-request coverage-source witness"
  witness :=
    { requestKey := "forged-analysis"
      targetKeySuffix := "forged-target"
      targetDescription := "forged target"
      targetLabel := "axial descriptor"
      kind := HostMoleculeTargetWitnessKind.noncenterDescriptor
      coverageField := HostMoleculeTargetCoverageField.axial
      observedCount := 1
      requiredCount := 1
      coverageChecked := true
      theoremFamilyKeys := ["forged-analysis::host-claim-stereo-element-mirror"] }
  fileName := "HostMoleculeTargetWitness_kforged_x45_analysis_kaxial_kforged_x45_target.lean"
  namespacePath := ["TetraStereoGenerated", "Examples", "ForgedWitnesses"]
  definitionName := "hostMoleculeTargetWitness_kforged_x45_analysis_kaxial_kforged_x45_target"
  theoremName := "host_molecule_target_witness_kforged_x45_analysis_kaxial_kforged_x45_target_checked"
  coverageSourceModule :=
    "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter"
  coverageSourcePacketName :=
    "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterPacket"
  coverageSourceAnnotationsName :=
    "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterBlueprint.annotations"
  coverageSourceBlueprintName :=
    "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterBlueprint"
  coverageSourceOwnerName :=
    "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.hostOfficialStereoOwnerRequestKey"
  coverageTheoremName := "host_molecule_target_witness_kforged_x45_analysis_kaxial_kforged_x45_target_coverage"
  dependencyTheoremNames :=
    ["TetraStereoGenerated.Examples.ForgedCrossRequestClaims.host_stereo_element_mirror_involutive"]
  imports :=
    [ "TetraStereo.Engine.HostAnalysisRequestBuilder"
    , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter"
    , "TetraStereoGenerated.Examples.ForgedCrossRequestClaims.HostStereoElementMirrorClaim" ]

/-- A suite cannot reuse another molecule request's host module as its witness coverage source. -/
def forgedCrossRequestCoverageSourceSuite : HostAnalysisSuiteRequest where
  key := "forged-analysis"
  description := "forged cross-request coverage-source suite"
  officialStereoRequests := broadSurfaceMoleculeAnalysisRequest.officialStereoRequests
  claimRequests := [forgedCrossRequestSourceClaimRequest]
  witnessRequests := [forgedCrossRequestSourceWitnessRequest]

/-- Coverage source packages must be scoped to the same host request as the target certificate. -/
theorem forgedCrossRequestCoverageSourceSuite_rejected :
    (match forgedCrossRequestCoverageSourceSuite.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by
    have hcoverage : validationFailed
        (forgedCrossRequestCoverageSourceSuite.validateWitnessCoverageSourceShape
          forgedCrossRequestSourceWitnessRequest broadSurfaceOfficialSourceRequest) := by
      refine ⟨"host analysis suite target witness coverage source owner does not match the witness request", ?_⟩
      unfold HostAnalysisSuiteRequest.validateWitnessCoverageSourceShape
      rfl
    have hwitness : validationFailed
        (forgedCrossRequestCoverageSourceSuite.validateWitnessRequestShape
          forgedCrossRequestSourceWitnessRequest) := by
      unfold HostAnalysisSuiteRequest.validateWitnessRequestShape
      rw [show forgedCrossRequestCoverageSourceSuite.officialRequestByModule?
          forgedCrossRequestSourceWitnessRequest.coverageSourceModule =
        some broadSurfaceOfficialSourceRequest by rfl]
      apply validation_failed_before
      apply validation_failed_before
      apply validation_failed_before
      apply validation_failed_after
      exact hcoverage
    have hsuite := validation_failed_of_single_witness
      forgedCrossRequestCoverageSourceSuite forgedCrossRequestSourceWitnessRequest
      (by rfl) hwitness
    rcases hsuite with ⟨message, hresult⟩
    rw [hresult]

/-- A nested request's official package key has the old prefix shape but a different exact owner. -/
def forgedPrefixAmbiguousCoverageSourceOfficialRequest : HostOfficialStereoRequest :=
  { broadSurfaceMoleculeAnalysisRequest.officialStereoRequest broadSurfaceOfficialCenterTarget with
    key := "forged-analysis::nested::official-center-comparison"
    ownerRequestKey := "forged-analysis::nested"
    packageKeySuffix := "official-center-comparison"
    moduleFileName := "ForgedNestedOfficialHost.lean"
    namespacePath :=
      ["TetraStereoGenerated", "Examples", "ForgedNestedSource", "Modules", "NestedOfficial"]
    definitionPrefix := "forgedNestedOfficial"
    certificateFileName := "ForgedNestedOfficialCertificate.lean"
    certificateTheoremName := "forged_nested_official_stereo_query_checked" }

/-- Witness body for the prefix-ambiguous source regression. -/
def forgedPrefixAmbiguousSourceWitness : HostMoleculeTargetWitness where
  requestKey := "forged-analysis"
  targetKeySuffix := "prefix-ambiguous-source"
  targetDescription := "prefix-ambiguous source"
  targetLabel := "axial descriptor"
  kind := HostMoleculeTargetWitnessKind.noncenterDescriptor
  coverageField := HostMoleculeTargetCoverageField.axial
  observedCount := 1
  requiredCount := 1
  coverageChecked := true
  theoremFamilyKeys := ["forged-analysis::host-claim-stereo-element-mirror"]

/-- A witness using a source whose key starts with `forged-analysis::` but is owned by a nested key. -/
def forgedPrefixAmbiguousSourceWitnessRequest : HostMoleculeTargetWitnessRequest where
  key := forgedPrefixAmbiguousSourceWitness.expectedPackageKey
  description := "forged prefix-ambiguous coverage-source witness"
  witness := forgedPrefixAmbiguousSourceWitness
  fileName := forgedPrefixAmbiguousSourceWitness.expectedFileName
  namespacePath := ["TetraStereoGenerated", "Examples", "ForgedWitnesses"]
  definitionName := forgedPrefixAmbiguousSourceWitness.expectedDefinitionName
  theoremName := forgedPrefixAmbiguousSourceWitness.expectedTheoremName
  coverageSourceModule := forgedPrefixAmbiguousCoverageSourceOfficialRequest.moduleName
  coverageSourcePacketName :=
    HostAnalysisSuiteRequest.officialCoveragePacketName
      forgedPrefixAmbiguousCoverageSourceOfficialRequest
  coverageSourceAnnotationsName :=
    HostAnalysisSuiteRequest.officialCoverageAnnotationsName
      forgedPrefixAmbiguousCoverageSourceOfficialRequest
  coverageSourceBlueprintName :=
    HostAnalysisSuiteRequest.officialCoverageBlueprintName
      forgedPrefixAmbiguousCoverageSourceOfficialRequest
  coverageSourceOwnerName :=
    HostAnalysisSuiteRequest.officialCoverageOwnerRequestKeyName
      forgedPrefixAmbiguousCoverageSourceOfficialRequest
  coverageTheoremName := forgedPrefixAmbiguousSourceWitness.expectedCoverageTheoremName
  dependencyTheoremNames :=
    [HostAnalysisSuiteRequest.claimTheoremName forgedCrossRequestSourceClaimRequest]
  imports :=
    [ "TetraStereo.Engine.HostAnalysisRequestBuilder"
    , forgedPrefixAmbiguousCoverageSourceOfficialRequest.moduleName
    , HostAnalysisSuiteRequest.claimModuleName forgedCrossRequestSourceClaimRequest ]

/-- A suite cannot accept nested request ownership merely because the package key has a prefix. -/
def forgedPrefixAmbiguousCoverageSourceSuite : HostAnalysisSuiteRequest where
  key := "forged-analysis"
  description := "forged prefix-ambiguous coverage-source suite"
  officialStereoRequests := [forgedPrefixAmbiguousCoverageSourceOfficialRequest]
  claimRequests := [forgedCrossRequestSourceClaimRequest]
  witnessRequests := [forgedPrefixAmbiguousSourceWitnessRequest]

/-- Exact owner metadata closes the old prefix-ambiguity hole. -/
theorem forgedPrefixAmbiguousCoverageSourceSuite_rejected :
    (match forgedPrefixAmbiguousCoverageSourceSuite.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by rfl

/-! ### Coverage/refusal regression checks -/

/-- Duplicate package-selection suffixes are refused before generated files are written. -/
def duplicateBroadSurfacePlan : HostStereochemicalAnalysisPlan where
  outputs :=
    [ HostStereochemicalOutputTarget.noncenterDescriptor
        { keySuffix := "dup"
          description := "first duplicate key"
          family := HostNoncenterDescriptorFamily.axial }
    , HostStereochemicalOutputTarget.noncenterDescriptor
        { keySuffix := "dup"
          description := "second duplicate key"
          family := HostNoncenterDescriptorFamily.planar }
    ]


theorem duplicateBroadSurfacePlan_rejected :
    (match duplicateBroadSurfacePlan.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by rfl

/-- Coverage requests fail when the packet/annotations do not expose enough matching units. -/
def missingCumulenePlan : HostStereochemicalAnalysisPlan where
  outputs :=
    [ HostStereochemicalOutputTarget.noncenterDescriptor
        { keySuffix := "needs-more-cumulenes"
          description := "requires more cumulene paths than broad fixture has"
          family := HostNoncenterDescriptorFamily.cumulene
          minimumCount := 2 } ]

/-- Missing cumulene coverage is refused. -/
theorem missingCumulenePlan_rejected :
    (match missingCumulenePlan.validateCoverage broadSurfaceMoleculeAnalysisRequest.detectorCoverage with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by rfl

/-- Exact descriptor requests fail when the family and descriptor payload disagree. -/
def mismatchedDescriptorResultPlan : HostStereochemicalAnalysisPlan where
  outputs :=
    [ HostStereochemicalOutputTarget.noncenterDescriptor
        { keySuffix := "bad-result-family"
          description := "axial target carrying a helical descriptor result"
          family := HostNoncenterDescriptorFamily.axial
          expectedResult? := some (HostMoleculeDescriptorResult.helical HelicalDescriptor.M) } ]

/-- Descriptor-result payloads must match their target family. -/
theorem mismatchedDescriptorResultPlan_rejected :
    (match mismatchedDescriptorResultPlan.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by rfl

/-- Exact descriptor requests fail when the requested descriptor value is absent from source data. -/
def missingExactAxialDescriptorPlan : HostStereochemicalAnalysisPlan where
  outputs :=
    [ HostStereochemicalOutputTarget.noncenterDescriptor
        { keySuffix := "missing-axial-sa"
          description := "requires an S_a axis but the source has R_a"
          family := HostNoncenterDescriptorFamily.axial
          expectedResult? := some (HostMoleculeDescriptorResult.axial AxialDescriptor.Sa)
          expectedSourceKey? :=
            some (HostMoleculeDescriptorSourceKey.axial 5 7 1 2 3 4) } ]

/-- Missing exact descriptor values are rejected at the molecule-analysis boundary. -/
theorem missingExactAxialDescriptorPlan_rejected :
    (match missingExactAxialDescriptorPlan.validateDescriptorResults
        broadSurfaceMoleculeAnalysisRequest.detectorCoverage
        broadSurfaceMoleculeAnalysisRequest.packet
        broadSurfaceMoleculeAnalysisRequest.annotations with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by rfl

/-- Source-unit keys without an exact descriptor/result request are rejected as ambiguous. -/
def orphanSourceKeyPlan : HostStereochemicalAnalysisPlan where
  outputs :=
    [ HostStereochemicalOutputTarget.noncenterDescriptor
        { keySuffix := "orphan-source"
          description := "source key supplied without an exact descriptor request"
          family := HostNoncenterDescriptorFamily.axial
          expectedSourceKey? :=
            some (HostMoleculeDescriptorSourceKey.axial 5 7 1 2 3 4) } ]

/-- A source key is only meaningful when bound to an exact descriptor/result target. -/
theorem orphanSourceKeyPlan_rejected :
    (match orphanSourceKeyPlan.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by rfl

/-- Auxiliary Rule-5 source keys must use the canonical support representative. -/
def noncanonicalAuxiliarySourceKeyPlan : HostStereochemicalAnalysisPlan where
  outputs :=
    [ HostStereochemicalOutputTarget.noncenterDescriptor
        { keySuffix := "noncanonical-auxiliary-source"
          description := "attempts to certify an auxiliary node through a source-key alias"
          family := HostNoncenterDescriptorFamily.auxiliaryRule5
          expectedResult? :=
            some (HostMoleculeDescriptorResult.auxiliaryRule5
              OfficialRule5Descriptor.descriptorR.asAuxiliary)
          expectedSourceKey? :=
            some (HostMoleculeDescriptorSourceKey.auxiliaryRule5 1 [1, 0] (some 0)) } ]

/-- Public descriptor-result certificates reject non-canonical source-key aliases. -/
theorem noncanonicalAuxiliarySourceKeyPlan_rejected :
    (match noncanonicalAuxiliarySourceKeyPlan.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by rfl

/-- Ensemble source keys without an exact kind request are rejected as ambiguous. -/
def orphanEnsembleSourceKeyPlan : HostStereochemicalAnalysisPlan where
  outputs :=
    [ HostStereochemicalOutputTarget.ensembleClaim
        { keySuffix := "orphan-ensemble-source"
          description := "source key supplied without an exact ensemble kind request"
          kind := HostEnsembleClaimTargetKind.descriptorChiralRefutesAchiral
          expectedSourceKey? :=
            some (HostMoleculeDescriptorSourceKey.ensemble "" [0, 1, 2]) } ]

/-- Ensemble source keys are only meaningful when bound to exact ensemble-kind evidence. -/
theorem orphanEnsembleSourceKeyPlan_rejected :
    (match orphanEnsembleSourceKeyPlan.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by rfl

/-- Unspecified double-bond stereo cannot be certified as an assigned alkene descriptor. -/
def unspecifiedAlkeneDescriptorPlan : HostStereochemicalAnalysisPlan where
  outputs :=
    [ HostStereochemicalOutputTarget.noncenterDescriptor
        { keySuffix := "unspecified-alkene"
          description := "attempts to certify unspecified alkene stereo"
          family := HostNoncenterDescriptorFamily.alkene
          expectedResult? :=
            some (HostMoleculeDescriptorResult.alkene DoubleBondStereo.unspecified) } ]

/-- Unassigned alkene descriptor requests fail generated-shape validation. -/
theorem unspecifiedAlkeneDescriptorPlan_rejected :
    (match unspecifiedAlkeneDescriptorPlan.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by rfl

/-- Chiral conformer claim targets cannot authenticate a nonstereogenic exact kind. -/
def nonstereogenicConformerKindPlan : HostStereochemicalAnalysisPlan where
  outputs :=
    [ HostStereochemicalOutputTarget.conformerClaim
        { keySuffix := "nonstereogenic-conformer"
          description := "attempts to bind a chiral conformer claim to nonstereogenic evidence"
          kind := HostConformerClaimTargetKind.profileChiralRefutesAchiral
          expectedKind? := some OfficialStereogenicUnitKind.nonstereogenic } ]

/-- Nonstereogenic conformer kinds are rejected for chiral conformer claim targets. -/
theorem nonstereogenicConformerKindPlan_rejected :
    (match nonstereogenicConformerKindPlan.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by rfl

/-- Chiral ensemble claim targets cannot authenticate a nonstereogenic exact kind. -/
def nonstereogenicEnsembleKindPlan : HostStereochemicalAnalysisPlan where
  outputs :=
    [ HostStereochemicalOutputTarget.ensembleClaim
        { keySuffix := "nonstereogenic-ensemble"
          description := "attempts to bind a descriptor-chiral ensemble claim to nonstereogenic evidence"
          kind := HostEnsembleClaimTargetKind.descriptorChiralRefutesAchiral
          expectedKind? := some OfficialStereogenicUnitKind.nonstereogenic } ]

/-- Nonstereogenic ensemble kinds are rejected for descriptor-chiral ensemble claim targets. -/
theorem nonstereogenicEnsembleKindPlan_rejected :
    (match nonstereogenicEnsembleKindPlan.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by rfl

/-- Deliberately invalid request whose official package key collides with a derived broad claim. -/
def packageKeyCollisionAnalysisRequest : HostMoleculeAnalysisRequest :=
  { broadSurfaceMoleculeAnalysisRequest with
    officialStereoTargets :=
      [ { broadSurfaceOfficialCenterTarget with
          keySuffix := HostStereoClaimTarget.officialCIPAssignmentSuccessResolved.defaultKey } ]
    analysisPlan := {}
    broadClaimPolicy :=
      HostBroadClaimPolicy.selected
        [HostStereoClaimTarget.officialCIPAssignmentSuccessResolved] }

/-- Cross-family package-key collisions are rejected after request expansion. -/
theorem packageKeyCollisionAnalysisRequest_rejected :
    (match packageKeyCollisionAnalysisRequest.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true :=
  by rfl

/-- Deliberately invalid broad claim whose key collides with an axial target certificate. -/
def certificateKeyCollisionClaimRequest : HostStereoClaimRequest where
  target := HostAnalysisRequestKernelProof.certificateKeyCollisionClaimRequest.target
  key := HostAnalysisRequestKernelProof.certificateKeyCollisionClaimRequest.key
  description := HostAnalysisRequestKernelProof.certificateKeyCollisionClaimRequest.description
  namespacePath := HostAnalysisRequestKernelProof.certificateKeyCollisionClaimRequest.namespacePath

/-- Deliberately invalid suite with an extra broad claim equal to a target-certificate key. -/
def certificateKeyCollisionSuiteRequest : HostAnalysisSuiteRequest :=
  HostAnalysisRequestKernelProof.certificateKeyCollisionSuiteRequest

/-- Public target-certificate keys participate in suite package-key collision checks. -/
abbrev certificateKeyCollisionSuiteRequest_rejected :=
  HostAnalysisRequestKernelProof.certificateKeyCollisionSuiteRequest_rejected

/-- Invalid indexed annotations are not counted as detector coverage. -/
def invalidAxisAnnotations : IndexedNoncenterStereoAnnotations :=
  { broadSurfaceAnnotations with
    axes :=
      [ { axisStart := 999
          axisEnd := 7
          startHigh := 1
          startLow := 2
          endHigh := 3
          endLow := 4
          descriptor := AxialDescriptor.Ra } ] }

/-- Out-of-range axial annotations do not satisfy axial coverage. -/
theorem invalidAxisAnnotations_not_counted :
    (HostDetectorCoverage.ofPacketAndAnnotations
      (rawMoleculePacket broadSurfaceRaw ChemistryImportTrust.proofCertifiedAdapter)
      invalidAxisAnnotations).axes = 0 :=
  rfl

/-- Conflicting descriptors on the same indexed axial geometry count as one physical unit. -/
def conflictingAxisAnnotations : IndexedNoncenterStereoAnnotations :=
  { broadSurfaceAnnotations with
    axes :=
      [ { axisStart := 5
          axisEnd := 7
          startHigh := 1
          startLow := 2
          endHigh := 3
          endLow := 4
          descriptor := AxialDescriptor.Ra }
      , { axisStart := 5
          axisEnd := 7
          startHigh := 1
          startLow := 2
          endHigh := 3
          endLow := 4
          descriptor := AxialDescriptor.Sa } ] }

/-- Geometry-key deduplication prevents descriptor conflicts from inflating axial coverage. -/
theorem conflictingAxisAnnotations_count_once :
    (HostDetectorCoverage.ofPacketAndAnnotations
      (rawMoleculePacket broadSurfaceRaw ChemistryImportTrust.proofCertifiedAdapter)
      conflictingAxisAnnotations).axes = 1 :=
  rfl

/-- Conflicting descriptors on the same geometry refuse both exact axial results. -/
theorem conflictingAxisAnnotations_exact_results_refused :
    ( HostMoleculeDescriptorResult.axialDescriptorCount
        (rawMoleculePacket broadSurfaceRaw ChemistryImportTrust.proofCertifiedAdapter)
        conflictingAxisAnnotations AxialDescriptor.Ra
    , HostMoleculeDescriptorResult.axialDescriptorCount
        (rawMoleculePacket broadSurfaceRaw ChemistryImportTrust.proofCertifiedAdapter)
        conflictingAxisAnnotations AxialDescriptor.Sa ) = (0, 0) :=
  rfl

/-- Nonchiral conformer/ensemble kinds cannot be used as assigned public chiral evidence. -/
theorem nonchiral_state_descriptor_results_not_assigned :
    ( (HostMoleculeDescriptorResult.conformerKind
          OfficialStereogenicUnitKind.nonstereogenic).assigned
    , (HostMoleculeDescriptorResult.ensembleKind
          OfficialStereogenicUnitKind.nonstereogenic).assigned ) = (false, false) :=
  rfl

/-- Auxiliary records whose raw support differs only by an included anchor canonicalize together. -/
def duplicateAuxiliaryRule5Annotations : IndexedNoncenterStereoAnnotations :=
  { broadSurfaceAnnotations with
    auxiliaryRule5Nodes :=
      [ { anchor := 1
          support := [0]
          descriptor := OfficialRule5Descriptor.descriptorR }
      , { anchor := 1
          support := [0, 1]
          descriptor := OfficialRule5Descriptor.descriptorR } ] }

/-- Canonical virtual-node support prevents duplicate auxiliary records from inflating coverage. -/
theorem duplicateAuxiliaryRule5Annotations_count_once :
    (HostDetectorCoverage.ofPacketAndAnnotations broadSurfaceMoleculeAnalysisRequest.packet
      duplicateAuxiliaryRule5Annotations).auxiliaryRule5Nodes = 1 :=
  by rfl

/-- Canonical virtual-node support also prevents duplicate auxiliary exact-result inflation. -/
theorem duplicateAuxiliaryRule5Annotations_keyed_exact_count_once :
    HostMoleculeDescriptorResult.auxiliaryRule5DescriptorCountForKey
      broadSurfaceMoleculeAnalysisRequest.packet duplicateAuxiliaryRule5Annotations
      (HostMoleculeDescriptorSourceKey.auxiliaryRule5 1 [0] (some 0))
      OfficialRule5Descriptor.descriptorR.asAuxiliary = 1 :=
  by rfl

/-- Auxiliary root distance is part of virtual-node identity. -/
def distinctRootAuxiliaryRule5Annotations : IndexedNoncenterStereoAnnotations :=
  { broadSurfaceAnnotations with
    auxiliaryRule5Nodes :=
      [ { anchor := 1
          support := [0]
          descriptor := OfficialRule5Descriptor.descriptorR
          rootDistance? := some 0 }
      , { anchor := 1
          support := [0]
          descriptor := OfficialRule5Descriptor.descriptorS
          rootDistance? := some 1 } ] }

/-- Distinct auxiliary root distances do not collapse into one contradictory descriptor source. -/
theorem distinctRootAuxiliaryRule5Annotations_keyed_counts_separately :
    ( (HostDetectorCoverage.ofPacketAndAnnotations broadSurfaceMoleculeAnalysisRequest.packet
          distinctRootAuxiliaryRule5Annotations).auxiliaryRule5Nodes
    , HostMoleculeDescriptorResult.auxiliaryRule5DescriptorCountForKey
        broadSurfaceMoleculeAnalysisRequest.packet distinctRootAuxiliaryRule5Annotations
        (HostMoleculeDescriptorSourceKey.auxiliaryRule5 1 [0] (some 0))
        OfficialRule5Descriptor.descriptorR.asAuxiliary
    , HostMoleculeDescriptorResult.auxiliaryRule5DescriptorCountForKey
        broadSurfaceMoleculeAnalysisRequest.packet distinctRootAuxiliaryRule5Annotations
        (HostMoleculeDescriptorSourceKey.auxiliaryRule5 1 [0] (some 1))
        OfficialRule5Descriptor.descriptorS.asAuxiliary ) = (2, 1, 1) :=
  by rfl

/-- Conformer support lists that differ only by order denote the same proof-facing support set. -/
def reorderedConformationAnnotations : IndexedNoncenterStereoAnnotations :=
  { broadSurfaceAnnotations with
    conformations :=
      [ { support := [0, 1, 2]
          kind? := some OfficialStereogenicUnitKind.chiral }
      , { support := [2, 1, 0]
          kind? := some OfficialStereogenicUnitKind.nonstereogenic } ] }

private def reorderedConformationChiral : IndexedDetectedConformationalState :=
  { support := [0, 1, 2]
    kind? := some OfficialStereogenicUnitKind.chiral }

private def reorderedConformationNonstereogenic : IndexedDetectedConformationalState :=
  { support := [2, 1, 0]
    kind? := some OfficialStereogenicUnitKind.nonstereogenic }

private theorem reorderedConformation_key_eq :
    HostDetectorCoverage.conformationKey reorderedConformationChiral =
      HostDetectorCoverage.conformationKey reorderedConformationNonstereogenic := by
  simp [reorderedConformationChiral, reorderedConformationNonstereogenic,
    HostDetectorCoverage.conformationKey, HostDetectorCoverage.stateIdentityKey,
    HostDetectorCoverage.atomSupportKey]
  ext atom
  simp only [Finset.mem_insert, Finset.mem_singleton]
  aesop

private theorem reorderedConformation_support_eq :
    HostDetectorCoverage.atomSupportKey reorderedConformationChiral.support =
      HostDetectorCoverage.atomSupportKey reorderedConformationNonstereogenic.support := by
  simp [reorderedConformationChiral, reorderedConformationNonstereogenic,
    HostDetectorCoverage.atomSupportKey]
  ext atom
  simp only [Finset.mem_insert, Finset.mem_singleton]
  aesop

/-- Set-key deduplication prevents reordered supports from inflating conformer coverage. -/
theorem reorderedConformationAnnotations_count_once :
    (HostDetectorCoverage.ofPacketAndAnnotations
      (rawMoleculePacket broadSurfaceRaw ChemistryImportTrust.proofCertifiedAdapter)
      reorderedConformationAnnotations).conformations = 1 :=
  by
    change (deduplicateByEquality
      (([reorderedConformationChiral, reorderedConformationNonstereogenic].filter
        (HostDetectorCoverage.conformationOK broadSurfaceRaw)).map
          HostDetectorCoverage.conformationKey)).length = 1
    have hchiral : HostDetectorCoverage.conformationOK broadSurfaceRaw
        reorderedConformationChiral = true := by rfl
    have hnonstereogenic : HostDetectorCoverage.conformationOK broadSurfaceRaw
        reorderedConformationNonstereogenic = true := by rfl
    simp [hchiral, hnonstereogenic, reorderedConformation_key_eq,
      deduplicateByEquality, deduplicateByEqualityAux, listContainsByEquality]

/-- Conflicting conformer kinds under the same implicit state key refuse both exact kinds. -/
theorem reorderedConformationAnnotations_exact_kinds_refused :
    ( HostMoleculeDescriptorResult.conformerKindCount
        broadSurfaceMoleculeAnalysisRequest.packet reorderedConformationAnnotations
        OfficialStereogenicUnitKind.chiral
    , HostMoleculeDescriptorResult.conformerKindCount
        broadSurfaceMoleculeAnalysisRequest.packet reorderedConformationAnnotations
        OfficialStereogenicUnitKind.nonstereogenic ) = (0, 0) :=
  by
    change
      ( HostDetectorCoverage.countUniqueStateKeysWithExactKind
          (HostDetectorCoverage.conformationOK broadSurfaceRaw)
          HostDetectorCoverage.conformationKey
          (fun record => HostDetectorCoverage.atomSupportKey record.support)
          (fun record => record.kind?) OfficialStereogenicUnitKind.chiral
          [reorderedConformationChiral, reorderedConformationNonstereogenic]
      , HostDetectorCoverage.countUniqueStateKeysWithExactKind
          (HostDetectorCoverage.conformationOK broadSurfaceRaw)
          HostDetectorCoverage.conformationKey
          (fun record => HostDetectorCoverage.atomSupportKey record.support)
          (fun record => record.kind?) OfficialStereogenicUnitKind.nonstereogenic
          [reorderedConformationChiral, reorderedConformationNonstereogenic] ) = (0, 0)
    have hchiral : HostDetectorCoverage.conformationOK broadSurfaceRaw
        reorderedConformationChiral = true := by rfl
    have hnonstereogenic : HostDetectorCoverage.conformationOK broadSurfaceRaw
        reorderedConformationNonstereogenic = true := by rfl
    unfold HostDetectorCoverage.countUniqueStateKeysWithExactKind
    simp only [List.filter_cons, hchiral, hnonstereogenic, if_true, List.filter_nil,
      List.map_cons, List.map_nil]
    rw [← reorderedConformation_key_eq]
    simp [deduplicateByEquality, deduplicateByEqualityAux, listContainsByEquality,
      reorderedConformation_support_eq]
    simp [reorderedConformationChiral, reorderedConformationNonstereogenic,
      deduplicateByEqualityAux, listContainsByEquality]

/-- Explicit conformer state IDs let distinct states share an atom support without collapsing. -/
def stateIdConformationAnnotations : IndexedNoncenterStereoAnnotations :=
  { broadSurfaceAnnotations with
    conformations :=
      [ { stateId := "chair-a"
          support := [0, 1, 2]
          kind? := some OfficialStereogenicUnitKind.chiral }
      , { stateId := "chair-b"
          support := [2, 1, 0]
          kind? := some OfficialStereogenicUnitKind.nonstereogenic } ] }

/-- Distinct explicit conformer state IDs count as separate exact kind-bearing states. -/
theorem stateIdConformationAnnotations_exact_kinds_count_separately :
    ( HostMoleculeDescriptorResult.conformerKindCount
        broadSurfaceMoleculeAnalysisRequest.packet stateIdConformationAnnotations
        OfficialStereogenicUnitKind.chiral
    , HostMoleculeDescriptorResult.conformerKindCount
        broadSurfaceMoleculeAnalysisRequest.packet stateIdConformationAnnotations
        OfficialStereogenicUnitKind.nonstereogenic ) = (1, 1) :=
  rfl

/-- Reusing one explicit conformer state ID for incompatible supports is treated as a conflict. -/
def sameIdConflictingConformationAnnotations : IndexedNoncenterStereoAnnotations :=
  { broadSurfaceAnnotations with
    conformations :=
      [ { stateId := "same-state"
          support := [0, 1]
          kind? := some OfficialStereogenicUnitKind.chiral }
      , { stateId := "same-state"
          support := [0, 1, 2]
          kind? := some OfficialStereogenicUnitKind.nonstereogenic } ] }

/-- Same-ID conformer support conflicts refuse both exact kind counts. -/
theorem sameIdConflictingConformationAnnotations_exact_kinds_refused :
    ( (HostDetectorCoverage.ofPacketAndAnnotations broadSurfaceMoleculeAnalysisRequest.packet
          sameIdConflictingConformationAnnotations).conformations
    , HostMoleculeDescriptorResult.conformerKindCount
        broadSurfaceMoleculeAnalysisRequest.packet sameIdConflictingConformationAnnotations
        OfficialStereogenicUnitKind.chiral
    , HostMoleculeDescriptorResult.conformerKindCount
        broadSurfaceMoleculeAnalysisRequest.packet sameIdConflictingConformationAnnotations
        OfficialStereogenicUnitKind.nonstereogenic ) = (1, 0, 0) :=
  by rfl

/-- Untyped same-ID conformer records still participate in support-stability checks. -/
def sameIdUntypedSupportConflictConformationAnnotations : IndexedNoncenterStereoAnnotations :=
  { broadSurfaceAnnotations with
    conformations :=
      [ { stateId := "same-state"
          support := [0, 1]
          kind? := some OfficialStereogenicUnitKind.chiral }
      , { stateId := "same-state"
          support := [0, 1, 2]
          kind? := none } ] }

/-- Untyped same-ID conformer support conflicts block aggregate and exact source counts. -/
theorem sameIdUntypedSupportConflictConformationAnnotations_refused :
    ( (HostDetectorCoverage.ofPacketAndAnnotations broadSurfaceMoleculeAnalysisRequest.packet
          sameIdUntypedSupportConflictConformationAnnotations).conformations
    , HostMoleculeDescriptorResult.conformerKindCount
        broadSurfaceMoleculeAnalysisRequest.packet
        sameIdUntypedSupportConflictConformationAnnotations OfficialStereogenicUnitKind.chiral
    , HostMoleculeDescriptorResult.conformerKindCountForKey
        broadSurfaceMoleculeAnalysisRequest.packet
        sameIdUntypedSupportConflictConformationAnnotations
        (HostMoleculeDescriptorSourceKey.conformer "same-state" [0, 1])
        OfficialStereogenicUnitKind.chiral ) = (1, 0, 0) :=
  by rfl

/-- Conflicting ensemble kinds under the same implicit state key refuse both exact kinds. -/
def reorderedEnsembleAnnotations : IndexedNoncenterStereoAnnotations :=
  { broadSurfaceAnnotations with
    ensembles :=
      [ { support := [0, 1, 2]
          kind? := some OfficialStereogenicUnitKind.chiral }
      , { support := [2, 1, 0]
          kind? := some OfficialStereogenicUnitKind.nonstereogenic } ] }

private def reorderedEnsembleChiral : IndexedDetectedEnsembleState :=
  { support := [0, 1, 2]
    kind? := some OfficialStereogenicUnitKind.chiral }

private def reorderedEnsembleNonstereogenic : IndexedDetectedEnsembleState :=
  { support := [2, 1, 0]
    kind? := some OfficialStereogenicUnitKind.nonstereogenic }

private theorem reorderedEnsemble_key_eq :
    HostDetectorCoverage.ensembleKey reorderedEnsembleChiral =
      HostDetectorCoverage.ensembleKey reorderedEnsembleNonstereogenic := by
  simp [reorderedEnsembleChiral, reorderedEnsembleNonstereogenic,
    HostDetectorCoverage.ensembleKey, HostDetectorCoverage.stateIdentityKey,
    HostDetectorCoverage.atomSupportKey]
  ext atom
  simp only [Finset.mem_insert, Finset.mem_singleton]
  aesop

private theorem reorderedEnsemble_support_eq :
    HostDetectorCoverage.atomSupportKey reorderedEnsembleChiral.support =
      HostDetectorCoverage.atomSupportKey reorderedEnsembleNonstereogenic.support := by
  simp [reorderedEnsembleChiral, reorderedEnsembleNonstereogenic,
    HostDetectorCoverage.atomSupportKey]
  ext atom
  simp only [Finset.mem_insert, Finset.mem_singleton]
  aesop

/-- Same-support conflicting ensemble kinds do not certify either exact kind. -/
theorem reorderedEnsembleAnnotations_exact_kinds_refused :
    ( HostMoleculeDescriptorResult.ensembleKindCount
        broadSurfaceMoleculeAnalysisRequest.packet reorderedEnsembleAnnotations
        OfficialStereogenicUnitKind.chiral
    , HostMoleculeDescriptorResult.ensembleKindCount
        broadSurfaceMoleculeAnalysisRequest.packet reorderedEnsembleAnnotations
        OfficialStereogenicUnitKind.nonstereogenic ) = (0, 0) :=
  by
    change
      ( HostDetectorCoverage.countUniqueStateKeysWithExactKind
          (HostDetectorCoverage.ensembleOK broadSurfaceRaw)
          HostDetectorCoverage.ensembleKey
          (fun record => HostDetectorCoverage.atomSupportKey record.support)
          (fun record => record.kind?) OfficialStereogenicUnitKind.chiral
          [reorderedEnsembleChiral, reorderedEnsembleNonstereogenic]
      , HostDetectorCoverage.countUniqueStateKeysWithExactKind
          (HostDetectorCoverage.ensembleOK broadSurfaceRaw)
          HostDetectorCoverage.ensembleKey
          (fun record => HostDetectorCoverage.atomSupportKey record.support)
          (fun record => record.kind?) OfficialStereogenicUnitKind.nonstereogenic
          [reorderedEnsembleChiral, reorderedEnsembleNonstereogenic] ) = (0, 0)
    have hchiral : HostDetectorCoverage.ensembleOK broadSurfaceRaw
        reorderedEnsembleChiral = true := by rfl
    have hnonstereogenic : HostDetectorCoverage.ensembleOK broadSurfaceRaw
        reorderedEnsembleNonstereogenic = true := by rfl
    unfold HostDetectorCoverage.countUniqueStateKeysWithExactKind
    simp only [List.filter_cons, hchiral, hnonstereogenic, if_true, List.filter_nil,
      List.map_cons, List.map_nil]
    rw [← reorderedEnsemble_key_eq]
    simp [deduplicateByEquality, deduplicateByEqualityAux, listContainsByEquality,
      reorderedEnsemble_support_eq]
    simp [reorderedEnsembleChiral, reorderedEnsembleNonstereogenic,
      deduplicateByEqualityAux, listContainsByEquality]

/-- Explicit ensemble state IDs let distinct ensemble states share support without collapsing. -/
def stateIdEnsembleAnnotations : IndexedNoncenterStereoAnnotations :=
  { broadSurfaceAnnotations with
    ensembles :=
      [ { stateId := "ensemble-a"
          support := [0, 1, 2]
          kind? := some OfficialStereogenicUnitKind.chiral }
      , { stateId := "ensemble-b"
          support := [2, 1, 0]
          kind? := some OfficialStereogenicUnitKind.nonstereogenic } ] }

/-- Distinct explicit ensemble state IDs count as separate exact kind-bearing states. -/
theorem stateIdEnsembleAnnotations_exact_kinds_count_separately :
    ( HostMoleculeDescriptorResult.ensembleKindCount
        broadSurfaceMoleculeAnalysisRequest.packet stateIdEnsembleAnnotations
        OfficialStereogenicUnitKind.chiral
    , HostMoleculeDescriptorResult.ensembleKindCount
        broadSurfaceMoleculeAnalysisRequest.packet stateIdEnsembleAnnotations
        OfficialStereogenicUnitKind.nonstereogenic ) = (1, 1) :=
  rfl

/-- Reusing one explicit ensemble state ID for incompatible supports is treated as a conflict. -/
def sameIdConflictingEnsembleAnnotations : IndexedNoncenterStereoAnnotations :=
  { broadSurfaceAnnotations with
    ensembles :=
      [ { stateId := "same-state"
          support := [0, 1]
          kind? := some OfficialStereogenicUnitKind.chiral }
      , { stateId := "same-state"
          support := [0, 1, 2]
          kind? := some OfficialStereogenicUnitKind.nonstereogenic } ] }

/-- Same-ID ensemble support conflicts refuse both exact kind counts. -/
theorem sameIdConflictingEnsembleAnnotations_exact_kinds_refused :
    ( (HostDetectorCoverage.ofPacketAndAnnotations broadSurfaceMoleculeAnalysisRequest.packet
          sameIdConflictingEnsembleAnnotations).ensembles
    , HostMoleculeDescriptorResult.ensembleKindCount
        broadSurfaceMoleculeAnalysisRequest.packet sameIdConflictingEnsembleAnnotations
        OfficialStereogenicUnitKind.chiral
    , HostMoleculeDescriptorResult.ensembleKindCount
        broadSurfaceMoleculeAnalysisRequest.packet sameIdConflictingEnsembleAnnotations
        OfficialStereogenicUnitKind.nonstereogenic ) = (1, 0, 0) :=
  by rfl

/-- Untyped same-ID ensemble records still participate in support-stability checks. -/
def sameIdUntypedSupportConflictEnsembleAnnotations : IndexedNoncenterStereoAnnotations :=
  { broadSurfaceAnnotations with
    ensembles :=
      [ { stateId := "same-state"
          support := [0, 1]
          kind? := some OfficialStereogenicUnitKind.chiral }
      , { stateId := "same-state"
          support := [0, 1, 2]
          kind? := none } ] }

/-- Untyped same-ID ensemble support conflicts block aggregate and exact source counts. -/
theorem sameIdUntypedSupportConflictEnsembleAnnotations_refused :
    ( (HostDetectorCoverage.ofPacketAndAnnotations broadSurfaceMoleculeAnalysisRequest.packet
          sameIdUntypedSupportConflictEnsembleAnnotations).ensembles
    , HostMoleculeDescriptorResult.ensembleKindCount
        broadSurfaceMoleculeAnalysisRequest.packet
        sameIdUntypedSupportConflictEnsembleAnnotations OfficialStereogenicUnitKind.chiral
    , HostMoleculeDescriptorResult.ensembleKindCountForKey
        broadSurfaceMoleculeAnalysisRequest.packet
        sameIdUntypedSupportConflictEnsembleAnnotations
        (HostMoleculeDescriptorSourceKey.ensemble "same-state" [0, 1])
        OfficialStereogenicUnitKind.chiral ) = (1, 0, 0) :=
  by rfl

/-- A naked double bond without perceived `E/Z` evidence is not an assigned alkene descriptor. -/
def unassignedAlkeneRaw : RawMolecule where
  atoms := List.replicate 4 (AtomSpec.aliphatic Element.C)
  bonds := [{ source := 0, target := 1, kind := ParsedBondKind.double }]

/-- Unassigned alkene candidates do not satisfy assigned-alkene coverage. -/
theorem unassignedAlkeneRaw_not_assigned :
    (HostDetectorCoverage.ofPacketAndAnnotations
      (rawMoleculePacket unassignedAlkeneRaw ChemistryImportTrust.proofCertifiedAdapter)
      {}).assignedDoubleBonds = 0 :=
  rfl

/-- Conflicting directional markers on one alkene side are ambiguous and must not certify `E/Z`. -/
def conflictingMarkerAlkeneRaw : RawMolecule where
  atoms := List.replicate 4 (AtomSpec.aliphatic Element.C)
  bonds :=
    [ { source := 0, target := 1, kind := ParsedBondKind.up }
    , { source := 0, target := 1, kind := ParsedBondKind.down }
    , { source := 1, target := 2, kind := ParsedBondKind.double }
    , { source := 2, target := 3, kind := ParsedBondKind.down }
    ]

/-- Ambiguous directional alkene input refuses both exact `E` and exact `Z` counts. -/
theorem conflictingMarkerAlkeneRaw_exact_ez_refused :
    ( HostMoleculeDescriptorResult.doubleBondStereoCount
        (rawMoleculePacket conflictingMarkerAlkeneRaw ChemistryImportTrust.proofCertifiedAdapter)
        DoubleBondStereo.E
    , HostMoleculeDescriptorResult.doubleBondStereoCount
        (rawMoleculePacket conflictingMarkerAlkeneRaw ChemistryImportTrust.proofCertifiedAdapter)
        DoubleBondStereo.Z ) = (0, 0) :=
  rfl

/-- Ambiguous directional alkene input also refuses generic assigned-alkene coverage. -/
theorem conflictingMarkerAlkeneRaw_not_assigned :
    (HostDetectorCoverage.ofPacketAndAnnotations
      (rawMoleculePacket conflictingMarkerAlkeneRaw ChemistryImportTrust.proofCertifiedAdapter)
      {}).assignedDoubleBonds = 0 :=
  rfl

end
end HostAnalysisRequestBuilder
end Examples
end TetraStereo
