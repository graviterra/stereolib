import TetraStereo.Examples.CertificateExport
import TetraStereo.Examples.CIPValidationFixtures
import TetraStereo.Examples.CHBrClF
import TetraStereo.Examples.OnePhenylethanol
import TetraStereo.Examples.MultiCenterDichloroButaneMeso
import TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcidTerminalSeeds
import TetraStereo.Examples.EngineIntake
import TetraStereo.Examples.PublicAPI
import TetraStereo.Examples.EngineTransaction
import TetraStereo.Examples.EngineRefusal
import TetraStereo.Examples.EngineClaims
import TetraStereo.Examples.OfficialStereoTransaction

set_option autoImplicit false

namespace TetraStereo
namespace Examples
namespace V01ClaimPackage

open OneCenter

noncomputable section






















structure V01CheckedDemoClaim where
  certificateArtifactsChecked :
    CertificateExport.exampleCertificateBatch.AllClaims
  officialCIPFixturesChecked :
    officialCIPEdgeFixtureBatch.AllClaims
  officialCIPFixtureCount :
    officialCIPEdgeFixtures.length = 14
  externalValidationIngestionChecked :
    externalValidationIngestionSeed.checkedFixtureBatch.AllClaims
  externalValidationCheckedCount :
    externalValidationIngestionSeed.checkedFixtures.length = 1
  externalValidationPendingCount :
    externalValidationIngestionSeed.pendingSpecs.length = 1
  chbrclfTwoAffineClasses :
    ∃ a b : StereoQ,
      a ≠ b ∧ ∀ c : StereoQ, c = a ∨ c = b
  -- Corrected calibration: the right-hand CHBrClF realization is `R`.
  chbrclfRightSafeR :
    CHBrClF.oneCenter.rs? bromochlorofluoromethaneRightRealization = some RS.R
  -- Historical field key retained; corrected statement: the right-hand value is `R`.
  chbrclfRightSafeS :
    CHBrClF.oneCenter.rs? bromochlorofluoromethaneRightRealization = some RS.R
  -- Corrected calibration: the left-hand CHBrClF realization is `S`.
  chbrclfLeftSafeS :
    CHBrClF.oneCenter.rs? bromochlorofluoromethaneLeftRealization = some RS.S
  -- Historical field key retained; corrected statement: the left-hand value is `S`.
  chbrclfLeftSafeR :
    CHBrClF.oneCenter.rs? bromochlorofluoromethaneLeftRealization = some RS.S
  onePhenylethanolOrder :
    OnePhenylethanol.oneCenter.cipOrderDescriptor = [0, 1, 2, 3]
  onePhenylethanolChiral :
    OnePhenylethanol.oneCenter.ChiralBySymmetry
  -- Corrected Cartesian calibration: the right-hand realization is `S`.
  onePhenylethanolRightSafeS :
    OnePhenylethanol.oneCenter.rsCIP? OnePhenylethanol.rightRealization = some RS.S
  -- Historical field key retained; corrected statement: the right-hand value is `S`.
  onePhenylethanolRightSafeR :
    OnePhenylethanol.oneCenter.rsCIP? OnePhenylethanol.rightRealization = some RS.S
  -- Corrected Cartesian calibration: the left-hand realization is `R`.
  onePhenylethanolLeftSafeR :
    OnePhenylethanol.oneCenter.rsCIP? OnePhenylethanol.leftRealization = some RS.R
  -- Historical field key retained; corrected statement: the left-hand value is `R`.
  onePhenylethanolLeftSafeS :
    OnePhenylethanol.oneCenter.rsCIP? OnePhenylethanol.leftRealization = some RS.R
  publicOnePhenylethanolPriorityResolved :
    OnePhenylethanol.oneCenter.ResolvedCIPDescriptor
  publicOnePhenylethanolRightSafeS :
    (Engine.descriptorRS OnePhenylethanol.oneCenter OnePhenylethanol.rightRealization).descriptor? =
      some RS.S
  -- Historical field key retained; corrected statement: the public right value is `S`.
  publicOnePhenylethanolRightSafeR :
    (Engine.descriptorRS OnePhenylethanol.oneCenter OnePhenylethanol.rightRealization).descriptor? =
      some RS.S
  publicOnePhenylethanolRightNeLeft :
    (Engine.descriptorRS OnePhenylethanol.oneCenter OnePhenylethanol.rightRealization).descriptor? ≠
      (Engine.descriptorRS OnePhenylethanol.oneCenter OnePhenylethanol.leftRealization).descriptor?
  publicOnePhenylethanolRightArtifactChecked :
    PublicAPI.onePhenylethanol_publicRightArtifact.claim
  engineOnePhenylethanolRightSafeS :
    EngineTransaction.onePhenylethanolEngineDemo.descriptor? = some RS.S
  -- Historical field key retained; corrected statement: the engine right value is `S`.
  engineOnePhenylethanolRightSafeR :
    EngineTransaction.onePhenylethanolEngineDemo.descriptor? = some RS.S
  engineOnePhenylethanolRightArtifactChecked :
    EngineTransaction.onePhenylethanolEngineCertified.artifact.claim
  engineOnePhenylethanolPriorityResolved :
    OnePhenylethanol.oneCenter.ResolvedCIPDescriptor
  engineMethaneRefusesTiedDescriptor :
    EngineRefusal.methaneEngineDecision.descriptor? = none
  engineMethaneRefusalArtifactChecked :
    EngineRefusal.methaneEngineCertifiedRefusal.artifact.claim
  engineMethaneNotDescriptorResolved :
    ¬ Methane.oneCenter.ResolvedCIPDescriptor
  engineOpenSMILESIntakeImported :
    EngineIntake.methaneOpenSMILESDecision.result?.isSome = true
  engineOpenSMILESIntakeArtifactChecked :
    EngineIntake.methaneOpenSMILESDecision.artifactClaim
  engineMolfileStringIntakeRefused :
    EngineIntake.molfileStringDecision.reason? =
      some
        (Engine.IntakeRefusalReason.importError
          (ChemistryImportError.externalBridgeRequired ChemistryImportFormat.molfileV2000))
  engineMalformedPacketIntakeRefused :
    EngineIntake.malformedBridgeDecision.reason? =
      some Engine.IntakeRefusalReason.rawMoleculeNotAdmissible
  publicOfficialCIPClaimArtifactChecked :
    EngineClaims.officialCIPClaimCertificate.artifact.claim
  publicMultiCenterClaimArtifactChecked :
    EngineClaims.multiCenterRelationClaimCertificate.artifact.claim
  publicGraphClaimArtifactChecked :
    EngineClaims.graphClassificationClaimCertificate.artifact.claim
  publicGraphRefusalClaimArtifactChecked :
    EngineClaims.graphClassificationRefusalCertificate.artifact.claim
  publicStereoElementClaimArtifactChecked :
    EngineClaims.stereoElementClaimCertificate.artifact.claim
  publicConformationalClaimArtifactChecked :
    EngineClaims.conformationalClaimCertificate.artifact.claim
  publicEnsembleClaimArtifactChecked :
    EngineClaims.ensembleClaimCertificate.artifact.claim
  publicOfficialStereoTransactionOutcome :
    OfficialStereoTransaction.helicalBranchDecision.outcome? = some Ordering.gt
  publicOfficialStereoTransactionArtifactChecked :
    OfficialStereoTransaction.helicalBranchCertificate.artifact.claim
  publicOfficialStereoGraphKeyOutcome :
    OfficialStereoTransaction.graphKeyDecision.outcome? = some Ordering.gt
  publicOfficialStereoGraphKeyArtifactChecked :
    OfficialStereoTransaction.graphKeyCertificate.artifact.claim
  publicOfficialStereoDefaultFuelOutcome :
    OfficialStereoTransaction.graphKeyDefaultFuelDecision.outcome? = some Ordering.gt
  publicOfficialStereoDefaultFuelArtifactChecked :
    OfficialStereoTransaction.graphKeyDefaultFuelCertificate.artifact.claim
  publicOfficialStereoMultipleBondOutcome :
    OfficialStereoTransaction.multipleBondDecision.outcome? = some Ordering.gt
  publicOfficialStereoMultipleBondArtifactChecked :
    OfficialStereoTransaction.multipleBondCertificate.artifact.claim
  publicOfficialStereoVirtualAuxiliaryOutcome :
    OfficialStereoTransaction.virtualAuxiliaryDecision.outcome? = some Ordering.gt
  publicOfficialStereoVirtualAuxiliaryArtifactChecked :
    OfficialStereoTransaction.virtualAuxiliaryCertificate.artifact.claim
  publicOfficialStereoRefusalArtifactChecked :
    OfficialStereoTransaction.emptyDetectorRefusal.artifact.claim
  publicOfficialStereoValidationIngestionChecked :
    OfficialStereoTransaction.officialStereoTransactionValidationIngestion.checkedFixtureBatch.AllClaims
  mesoMixedClass :
    DichloroButaneMesoToy.multi.MesoCipRSConfigurationBySymmetry
      DichloroButaneMesoToy.cfg
  mesoSameClassChiral :
    DichloroButaneMesoToy.multi.ChiralCipRSConfigurationBySymmetry
      DichloroButaneMesoToy.cfgSame
  mesoQuotientThreeClasses :
    ∃ a b c : DichloroButaneMesoToy.multi.CipRSPatternQ,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        ∀ q : DichloroButaneMesoToy.multi.CipRSPatternQ, q = a ∨ q = b ∨ q = c

  pseudoTerminalLeftSeed :
    PseudoasymmetricTrihydroxyglutaricAcid.safeDescriptorSeedState.rs
      PseudoasymmetricTrihydroxyglutaricAcid.leftCenter = some RS.S

  pseudoTerminalRightSeed :
    PseudoasymmetricTrihydroxyglutaricAcid.safeDescriptorSeedState.rs
      PseudoasymmetricTrihydroxyglutaricAcid.rightCenter = some RS.R
  pseudoSelectorWritesMiddleR :
    PseudoasymmetricTrihydroxyglutaricAcid.pseudoasymmetricRule5TaskSelector.schedule.runOnce.pseudo
      PseudoasymmetricTrihydroxyglutaricAcid.middleCenter = some PseudoRS.r
  pseudoFinalWritesMiddleR :
    PseudoasymmetricTrihydroxyglutaricAcid.afterMiddleSafeDescriptorDiscoveryState.pseudo
      PseudoasymmetricTrihydroxyglutaricAcid.middleCenter = some PseudoRS.r
  pseudoConfigurationAchiral :
    PseudoasymmetricTrihydroxyglutaricAcid.multi.AchiralConfigurationBySymmetry
      PseudoasymmetricTrihydroxyglutaricAcid.cfg

/-- The concrete checked v0.1 demo package. -/
def checkedDemoClaim : V01CheckedDemoClaim where
  certificateArtifactsChecked :=
    CertificateExport.exampleCertificateBatch_checked
  officialCIPFixturesChecked :=
    officialCIPEdgeFixtureBatch_checked
  officialCIPFixtureCount :=
    officialCIPEdgeFixtures_length
  externalValidationIngestionChecked :=
    externalValidationIngestionSeed_checked
  externalValidationCheckedCount :=
    externalValidationIngestionSeed_checkedFixtures_length
  externalValidationPendingCount :=
    externalValidationIngestionSeed_pendingSpecs_length
  chbrclfTwoAffineClasses :=
    bromochlorofluoromethane_has_exactly_two_stereochemical_classes
  chbrclfRightSafeR :=
    CHBrClF.rs?_right_eq_some_R
  chbrclfRightSafeS :=
    CHBrClF.rs?_right_eq_some_S
  chbrclfLeftSafeS :=
    CHBrClF.rs?_left_eq_some_S
  chbrclfLeftSafeR :=
    CHBrClF.rs?_left_eq_some_R
  onePhenylethanolOrder :=
    OnePhenylethanol.cipOrderDescriptor_eq_expected
  onePhenylethanolChiral :=
    OnePhenylethanol.chiralBySymmetry_of_descriptorCIP
  onePhenylethanolRightSafeS :=
    OnePhenylethanol.rsCIP?_right_eq_some_S
  onePhenylethanolRightSafeR :=
    OnePhenylethanol.rsCIP?_right_eq_some_R
  onePhenylethanolLeftSafeR :=
    OnePhenylethanol.rsCIP?_left_eq_some_R
  onePhenylethanolLeftSafeS :=
    OnePhenylethanol.rsCIP?_left_eq_some_S
  publicOnePhenylethanolPriorityResolved :=
    PublicAPI.onePhenylethanol_publicPriority_success_resolved
  publicOnePhenylethanolRightSafeS :=
    PublicAPI.onePhenylethanol_publicRS_right_eq_some_S
  publicOnePhenylethanolRightSafeR :=
    PublicAPI.onePhenylethanol_publicRS_right_eq_some_R
  publicOnePhenylethanolRightNeLeft :=
    PublicAPI.onePhenylethanol_publicRS_right_descriptor_ne_left_descriptor
  publicOnePhenylethanolRightArtifactChecked :=
    PublicAPI.onePhenylethanol_publicRightArtifact_checked
  engineOnePhenylethanolRightSafeS :=
    EngineTransaction.onePhenylethanolEngineDemo_descriptor_eq_some_S
  engineOnePhenylethanolRightSafeR :=
    EngineTransaction.onePhenylethanolEngineDemo_descriptor_eq_some_R
  engineOnePhenylethanolRightArtifactChecked :=
    EngineTransaction.onePhenylethanolEngineDemo_checked
  engineOnePhenylethanolPriorityResolved :=
    EngineTransaction.onePhenylethanolEngineDemo_resolved
  engineMethaneRefusesTiedDescriptor :=
    EngineRefusal.methaneEngineDecision_descriptor_eq_none
  engineMethaneRefusalArtifactChecked :=
    EngineRefusal.methaneEngineRefusal_checked
  engineMethaneNotDescriptorResolved :=
    EngineRefusal.methaneEngineRefusal_not_resolved
  engineOpenSMILESIntakeImported :=
    EngineIntake.methaneOpenSMILESDecision_imported
  engineOpenSMILESIntakeArtifactChecked :=
    EngineIntake.methaneOpenSMILESDecision_checked
  engineMolfileStringIntakeRefused :=
    EngineIntake.molfileStringDecision_refused
  engineMalformedPacketIntakeRefused :=
    EngineIntake.malformedBridgeDecision_refused
  publicOfficialCIPClaimArtifactChecked :=
    EngineClaims.officialCIPClaimCertificate_checked
  publicMultiCenterClaimArtifactChecked :=
    EngineClaims.multiCenterRelationClaimCertificate_checked
  publicGraphClaimArtifactChecked :=
    EngineClaims.graphClassificationClaimCertificate_checked
  publicGraphRefusalClaimArtifactChecked :=
    EngineClaims.graphClassificationRefusalCertificate_checked
  publicStereoElementClaimArtifactChecked :=
    EngineClaims.stereoElementClaimCertificate_checked
  publicConformationalClaimArtifactChecked :=
    EngineClaims.conformationalClaimCertificate_checked
  publicEnsembleClaimArtifactChecked :=
    EngineClaims.ensembleClaimCertificate_checked
  publicOfficialStereoTransactionOutcome :=
    OfficialStereoTransaction.helicalBranchDecision_outcome_eq_some_gt
  publicOfficialStereoTransactionArtifactChecked :=
    OfficialStereoTransaction.helicalBranchCertificate_checked
  publicOfficialStereoGraphKeyOutcome :=
    OfficialStereoTransaction.graphKeyDecision_outcome_eq_some_gt
  publicOfficialStereoGraphKeyArtifactChecked :=
    OfficialStereoTransaction.graphKeyCertificate_checked
  publicOfficialStereoDefaultFuelOutcome :=
    OfficialStereoTransaction.graphKeyDefaultFuelDecision_outcome_eq_some_gt
  publicOfficialStereoDefaultFuelArtifactChecked :=
    OfficialStereoTransaction.graphKeyDefaultFuelCertificate_checked
  publicOfficialStereoMultipleBondOutcome :=
    OfficialStereoTransaction.multipleBondDecision_outcome_eq_some_gt
  publicOfficialStereoMultipleBondArtifactChecked :=
    OfficialStereoTransaction.multipleBondCertificate_checked
  publicOfficialStereoVirtualAuxiliaryOutcome :=
    OfficialStereoTransaction.virtualAuxiliaryDecision_outcome_eq_some_gt
  publicOfficialStereoVirtualAuxiliaryArtifactChecked :=
    OfficialStereoTransaction.virtualAuxiliaryCertificate_checked
  publicOfficialStereoRefusalArtifactChecked :=
    OfficialStereoTransaction.emptyDetectorRefusal_checked
  publicOfficialStereoValidationIngestionChecked :=
    OfficialStereoTransaction.officialStereoTransactionValidationIngestion_checked
  mesoMixedClass :=
    DichloroButaneMesoToy.cfg_mesoCipRSConfigurationBySymmetry
  mesoSameClassChiral :=
    DichloroButaneMesoToy.cfgSame_chiralCipRSConfigurationBySymmetry
  mesoQuotientThreeClasses :=
    DichloroButaneMesoToy.cipRSPatternQ_exactly_three_classes
  pseudoTerminalLeftSeed :=
    PseudoasymmetricTrihydroxyglutaricAcid.safeDescriptorSeedState_rs_left_eq_some_R
  pseudoTerminalRightSeed :=
    PseudoasymmetricTrihydroxyglutaricAcid.safeDescriptorSeedState_rs_right_eq_some_S
  pseudoSelectorWritesMiddleR :=
    PseudoasymmetricTrihydroxyglutaricAcid.pseudoasymmetricRule5TaskSelector_runOnce_middle_pseudo_eq_some_r
  pseudoFinalWritesMiddleR :=
    PseudoasymmetricTrihydroxyglutaricAcid.afterMiddleSafeDescriptorDiscoveryState_middle_pseudo_eq_some_r
  pseudoConfigurationAchiral :=
    PseudoasymmetricTrihydroxyglutaricAcid.achiralConfigurationBySymmetry

theorem checkedDemoClaim_officialCIPFixturesChecked :
    checkedDemoClaim.officialCIPFixturesChecked =
      officialCIPEdgeFixtureBatch_checked :=
  rfl

theorem checkedDemoClaim_certificateArtifactsChecked :
    checkedDemoClaim.certificateArtifactsChecked =
      CertificateExport.exampleCertificateBatch_checked :=
  rfl

end
end V01ClaimPackage
end Examples
end TetraStereo
