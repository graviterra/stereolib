import TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalBranchInverse
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false






























namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput
















theorem referenceState_generalRigidAutomorphism_label_sign_iff_of_physicalDomain
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (root : input.certified.Atom)
    (e : input.certified.detectedMultiCenterMolecule.Aut) (mirror : Bool)
    (rootFixed : (e : Equiv.Perm input.certified.Atom) root = root)
    (d : input.certified.detectedMultiCenterMolecule.Center)
    (t u : LocalizedUniversalReference.Occurrence input)
    (d_ne_root : d ≠ c)
    (image_ne_root : input.certified.detectedMultiCenterMolecule.centerPerm e d ≠ c)
    (d_notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule d)
    (image_notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule
        (input.certified.detectedMultiCenterMolecule.centerPerm e d))
    (tRoot : t.1.root = root) (uRoot : u.1.root = root)
    (tCurrent : t.1.node.current? = some d.1)
    (uCurrent : u.1.node.current? =
      some (input.certified.detectedMultiCenterMolecule.centerPerm e d).1) :
    LocalizedUniversalReference.referenceState input u =
      (if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id)
        (LocalizedUniversalReference.referenceState input t) ↔
      ActualLocalSignLaw input.certified.detectedMultiCenterMolecule cfg e mirror d := by
  classical
  let m : MultiCenterMolecule input.certified.Atom :=
    input.certified.detectedMultiCenterMolecule
  have calibratedD : ActualPhysicalGeneralRigidCalibratedCenter input.certified m cfg d := by
    rcases domain.centerCase d d_ne_root with twin | calibrated
    · exact absurd twin d_notTwin
    · exact calibrated
  have calibratedImage :
      ActualPhysicalGeneralRigidCalibratedCenter input.certified m cfg (m.centerPerm e d) := by
    rcases domain.centerCase (m.centerPerm e d) image_ne_root with twin | calibrated
    · exact absurd twin image_notTwin
    · exact calibrated
  obtain ⟨frameF, alphaF, pointAtF, frameComputedF, matchF, spatialF, _observedF,
    calibrationFNonempty⟩ :=
    ActualGeneralRigidPhysicalBranchInverse.exists_physicalFrameAndCalibration_of_physicalGeneralRigidCenter
      input singleBonded acyclic m rfl cfg d t tCurrent calibratedD
  obtain ⟨frameG, alphaG, pointAtG, frameComputedG, matchG, spatialG, _observedG,
    calibrationGNonempty⟩ :=
    ActualGeneralRigidPhysicalBranchInverse.exists_physicalFrameAndCalibration_of_physicalGeneralRigidCenter
      input singleBonded acyclic m rfl cfg (m.centerPerm e d) u uCurrent calibratedImage
  have derivedF : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame t frameF :=
    input.certified.localizedOccurrenceFourLigandFrame?_sound t frameF frameComputedF
  have derivedG : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame u frameG :=
    input.certified.localizedOccurrenceFourLigandFrame?_sound u frameG frameComputedG
  let centerF : input.certified.TetrahedralCenter := ⟨d.1, d.2⟩
  let centerU : input.certified.TetrahedralCenter := ⟨(m.centerPerm e d).1, (m.centerPerm e d).2⟩
  have centerRealF : input.certified.RealTetrahedralCenterNode t.1.node centerF :=
    ⟨carrierOccurrence_provenance_real input.certified singleBonded acyclic t, by
      simpa [centerF] using tCurrent⟩
  have centerRealU : input.certified.RealTetrahedralCenterNode u.1.node centerU :=
    ⟨carrierOccurrence_provenance_real input.certified singleBonded acyclic u, by
      simpa [centerU] using uCurrent⟩
  have rigidF : ConstitutionallyRigidGraphAt input.certified.moleculeGraph centerF.1 := by
    simpa [centerF] using
      constitutionallyRigidGraphAt_of_constitutionallyRigid_detected input.certified d
        calibratedD.1
  have rigidU : ConstitutionallyRigidGraphAt input.certified.moleculeGraph centerU.1 := by
    simpa [centerU] using
      constitutionallyRigidGraphAt_of_constitutionallyRigid_detected input.certified
        (m.centerPerm e d) calibratedImage.1
  obtain ⟨calibrationF⟩ := calibrationFNonempty
  obtain ⟨calibrationG⟩ := calibrationGNonempty
  have key := referenceState_generalRigidAutomorphism_label_sign_iff
    input noDouble singleBonded acyclic charge m rfl cfg d e mirror root rootFixed
    t u tRoot uRoot frameF frameG derivedF derivedG centerF centerU centerRealF centerRealU
    rfl rfl rigidF rigidU alphaF alphaG matchF matchG
    (fun i => pointAtF (alphaF i)) (fun i => pointAtG (alphaG i))
    (by simpa using spatialF) (by simpa using spatialG) calibrationF calibrationG
  simpa only [ActualLocalSignLaw] using key







theorem referenceState_generalRigidAutomorphism_label_of_physicalDomain
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (root : input.certified.Atom)
    (e : input.certified.detectedMultiCenterMolecule.Aut) (mirror : Bool)
    (rootFixed : (e : Equiv.Perm input.certified.Atom) root = root)
    (d : input.certified.detectedMultiCenterMolecule.Center)
    (t u : LocalizedUniversalReference.Occurrence input)
    (d_ne_root : d ≠ c)
    (image_ne_root : input.certified.detectedMultiCenterMolecule.centerPerm e d ≠ c)
    (d_notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule d)
    (image_notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule
        (input.certified.detectedMultiCenterMolecule.centerPerm e d))
    (tRoot : t.1.root = root) (uRoot : u.1.root = root)
    (tCurrent : t.1.node.current? = some d.1)
    (uCurrent : u.1.node.current? =
      some (input.certified.detectedMultiCenterMolecule.centerPerm e d).1)
    (signLaw : ActualLocalSignLaw input.certified.detectedMultiCenterMolecule cfg e mirror d) :
    LocalizedUniversalReference.referenceState input u =
      (if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id)
        (LocalizedUniversalReference.referenceState input t) :=
  (referenceState_generalRigidAutomorphism_label_sign_iff_of_physicalDomain
    input noDouble singleBonded acyclic charge cfg c domain root e mirror rootFixed d t u
    d_ne_root image_ne_root d_notTwin image_notTwin tRoot uRoot tCurrent uCurrent).mpr signLaw

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

/-! ## Public kernel guards -/

assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.referenceState_generalRigidAutomorphism_label_sign_iff_of_physicalDomain
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.referenceState_generalRigidAutomorphism_label_of_physicalDomain
