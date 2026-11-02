import TetraStereo.OneCenter.LocalizedActualReaderPhysicalBranchInverse
import TetraStereo.OneCenter.LocalizedGeneralRigidCalibratedRootReader
import TetraStereo.OneCenter.LocalizedGeneralRigidLabelCovariance
import TetraStereo.OneCenter.LocalizedPhysicalDomainAdapters
import TetraStereo.OneCenter.LocalizedActualPhysicalReferenceSelection
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false


















































namespace TetraStereo.OneCenter

namespace ActualGeneralRigidPhysicalBranchInverse

open CertifiedLocalizedCIPInput







/-- The actual final target occurrence of the original root carried by a detected center. -/
noncomputable def topTarget (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center) :
    LocalizedUniversalReference.Occurrence input :=
  ActualReaderPhysicalBranchInverse.topTarget input c

/-- The generated localized dependency reader at the final original-root target. -/
noncomputable def dependencyReader (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center) :
    input.certified.LocalizedRerootCursor (LocalizedUniversalReference.carrierFuel input) →
      Option LocalizedAuxiliaryLabel :=
  ActualReaderPhysicalBranchInverse.dependencyReader input c

/-- The actual final target still observes the detected center atom. -/
theorem topTarget_current (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center) :
    (topTarget input c).1.node.current? = some c.1 :=
  ActualReaderPhysicalBranchInverse.topTarget_current input c

/-- The actual final target still sits at the empty address. -/
theorem topTarget_address (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center) :
    (topTarget input c).1.address = [] :=
  ActualReaderPhysicalBranchInverse.topTarget_address input c

/-- The final target's root is the detected center atom.  This is the common root of every actual
position source of either realized tree, and it is the root fixed by the physical automorphism. -/
theorem topTarget_root (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center) :
    (topTarget input c).1.root = c.1 :=
  ActualReaderPhysicalBranchInverse.topTarget_root input c

















theorem exists_physicalFrameAndCalibration_of_physicalGeneralRigidCenter
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (m : MultiCenterMolecule input.certified.Atom)
    (molEq : m.mol = input.certified.moleculeGraph)
    (cfg : m.Configuration) (center : m.Center)
    (target : LocalizedUniversalReference.Occurrence input)
    (targetCurrent : target.1.node.current? = some center.1)
    (calibrated : ActualPhysicalGeneralRigidCalibratedCenter input.certified m cfg center) :
    ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (alpha : Equiv.Perm (Fin 4)) (pointAt : Fin 4 → CartesianPoint3),
      input.certified.localizedOccurrenceFourLigandFrame? target = some frame ∧
        ActualFrameLigandMatch input m frame center alpha ∧
        (∀ i, input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt i) =
          some (pointAt (alpha i))) ∧
        (∀ i, input.certified.spatialPointAt? (m.ligandAtomAt center i) = some (pointAt i)) ∧
        Nonempty (PhysicalFrameCalibration m cfg center alpha (fun i => pointAt (alpha i))) := by
  classical
  obtain ⟨_rigid, pointAt, observed, nonzero, signEq⟩ := calibrated
  obtain ⟨frame, alpha, frameComputed, ligandLink⟩ :=
    input.certified.exists_localizedOccurrenceFourLigandFrame_and_ligandPermutation
      singleBonded acyclic (globalCarrierFuel_adequate input) target targetCurrent
      m molEq center rfl
  have ligandMatch : ActualFrameLigandMatch input m frame center alpha :=
    { real := fun index =>
        carrierOccurrence_provenance_real input.certified singleBonded acyclic
          (frame.cursorAt index).occurrence
      atom := ligandLink }
  have spatial : ∀ i : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt i) =
        some (pointAt (alpha i)) := by
    intro i
    simp [localizedRerootCursorSpatialPoint?, ligandLink i, observed (alpha i)]
  refine ⟨frame, alpha, pointAt, frameComputed, ligandMatch, spatial, observed, ?_⟩
  exact
    ⟨{ physicalPointAt := pointAt
       calibrated := fun _i => rfl
       nondegenerate := nonzero
       sign_eq := signEq }⟩













theorem generalRigidCalibratedCenter_of_canonicalDomain
    (input : LocalizedUniversalReference.Input)
    (cfgCan : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domainCan : ActualGeneralRigidGlobalPhysicalDomain input.certified cfgCan c)
    (d : input.certified.detectedMultiCenterMolecule.Center)
    (d_ne_root : d ≠ c)
    (notTwin : ¬ RootedBranchTerminalTwinCompletion.HasTerminalTwins
      input.certified.detectedMultiCenterMolecule d) :
    ActualGeneralRigidCalibratedCenter input.certified cfgCan d := by
  have notTwinPhysical : ¬ ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule d :=
    fun twin => notTwin
      ((actualPhysicalTerminalTwinCenter_iff_hasTerminalTwins input.certified
        input.certified.detectedMultiCenterMolecule d).mp twin)
  exact actualGeneralRigidCalibratedCenter_of_globalDomain domainCan d_ne_root notTwinPhysical






theorem exists_generalRigidPositiveReadback_of_canonicalDomain
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfgCan : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domainCan : ActualGeneralRigidGlobalPhysicalDomain input.certified cfgCan c)
    (d : input.certified.detectedMultiCenterMolecule.Center)
    (d_ne_root : d ≠ c)
    (notTwin : ¬ RootedBranchTerminalTwinCompletion.HasTerminalTwins
      input.certified.detectedMultiCenterMolecule d)
    (t : LocalizedUniversalReference.Occurrence input)
    (tCurrent : t.1.node.current? = some d.1) :
    ∃ center : input.certified.TetrahedralCenter,
      ActualGeneralRigidPositiveReadback input cfgCan center t := by
  have calibrated : ActualGeneralRigidCalibratedCenter input.certified cfgCan d :=
    generalRigidCalibratedCenter_of_canonicalDomain input cfgCan c domainCan d d_ne_root notTwin
  exact ⟨d,
    actualGeneralRigidPositiveReadback_of_calibratedCenter input singleBonded acyclic hcharge
      noDouble cfgCan d t tCurrent calibrated⟩





theorem exists_chiral_referenceState_of_canonicalDomain
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfgCan : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domainCan : ActualGeneralRigidGlobalPhysicalDomain input.certified cfgCan c)
    (d : input.certified.detectedMultiCenterMolecule.Center)
    (d_ne_root : d ≠ c)
    (notTwin : ¬ RootedBranchTerminalTwinCompletion.HasTerminalTwins
      input.certified.detectedMultiCenterMolecule d)
    (t : LocalizedUniversalReference.Occurrence input)
    (tCurrent : t.1.node.current? = some d.1) :
    ∃ rs : RS, LocalizedUniversalReference.referenceState input t = some (.chiral rs) := by
  obtain ⟨_center, positive⟩ :=
    exists_generalRigidPositiveReadback_of_canonicalDomain input singleBonded acyclic hcharge
      noDouble cfgCan c domainCan d d_ne_root notTwin t tCurrent
  obtain ⟨rs, _tracked, _frame, _alpha, _pointAt, _current, _notTwin, _calibrated,
    _frameComputed, _ligandLink, _spatial, _observed, _calibration, _trackedOrder, _pseudo,
    state, _sign⟩ := positive
  exact ⟨rs, state⟩



theorem constitutionallyRigidGraphAt_of_canonicalDomain
    (input : LocalizedUniversalReference.Input)
    (cfgCan : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domainCan : ActualGeneralRigidGlobalPhysicalDomain input.certified cfgCan c)
    (d : input.certified.detectedMultiCenterMolecule.Center)
    (d_ne_root : d ≠ c)
    (notTwin : ¬ RootedBranchTerminalTwinCompletion.HasTerminalTwins
      input.certified.detectedMultiCenterMolecule d) :
    ConstitutionallyRigidGraphAt input.certified.moleculeGraph d.1 :=
  constitutionallyRigidGraphAt_of_generalRigidCalibratedCenter
    (generalRigidCalibratedCenter_of_canonicalDomain input cfgCan c domainCan d d_ne_root notTwin)

/-! ## The local sign correspondence -/














def GeneralRigidLocalSignCorrespondence
    (input : LocalizedUniversalReference.Input)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (root : input.certified.Atom)
    (e : input.certified.detectedMultiCenterMolecule.Aut) (mirror : Bool) : Prop :=
  (e : Equiv.Perm input.certified.Atom) root = root →
  ∀ (d : input.certified.detectedMultiCenterMolecule.Center)
      (t u : LocalizedUniversalReference.Occurrence input),
    d ≠ c →
    input.certified.detectedMultiCenterMolecule.centerPerm e d ≠ c →
    ¬ ActualPhysicalTerminalTwinCenter input.certified
        input.certified.detectedMultiCenterMolecule d →
    ¬ ActualPhysicalTerminalTwinCenter input.certified
        input.certified.detectedMultiCenterMolecule
          (input.certified.detectedMultiCenterMolecule.centerPerm e d) →
    t.1.root = root →
    u.1.root = root →
    t.1.node.current? = some d.1 →
    u.1.node.current? =
      some (input.certified.detectedMultiCenterMolecule.centerPerm e d).1 →
    LocalizedUniversalReference.referenceState input u =
      (if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id)
        (LocalizedUniversalReference.referenceState input t) →
    ActualLocalSignLaw input.certified.detectedMultiCenterMolecule cfg e mirror d





theorem generalRigidLocalSignCorrespondence_of_referenceState_iff
    (input : LocalizedUniversalReference.Input)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (root : input.certified.Atom)
    (e : input.certified.detectedMultiCenterMolecule.Aut) (mirror : Bool)
    (iffReaderSign : ∀ (d : input.certified.detectedMultiCenterMolecule.Center)
        (t u : LocalizedUniversalReference.Occurrence input),
      d ≠ c →
      input.certified.detectedMultiCenterMolecule.centerPerm e d ≠ c →
      ¬ ActualPhysicalTerminalTwinCenter input.certified
          input.certified.detectedMultiCenterMolecule d →
      ¬ ActualPhysicalTerminalTwinCenter input.certified
          input.certified.detectedMultiCenterMolecule
            (input.certified.detectedMultiCenterMolecule.centerPerm e d) →
      t.1.root = root →
      u.1.root = root →
      t.1.node.current? = some d.1 →
      u.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.centerPerm e d).1 →
      (LocalizedUniversalReference.referenceState input u =
        (if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id)
          (LocalizedUniversalReference.referenceState input t) ↔
        ActualLocalSignLaw input.certified.detectedMultiCenterMolecule cfg e mirror d)) :
    GeneralRigidLocalSignCorrespondence input cfg c root e mirror := by
  intro _rootFixed d t u d_ne_root image_ne_root d_notTwin image_notTwin tRoot uRoot
    tCurrent uCurrent stateRel
  exact (iffReaderSign d t u d_ne_root image_ne_root d_notTwin image_notTwin tRoot uRoot
    tCurrent uCurrent).mp stateRel










theorem generalRigidLocalSignCorrespondence_of_physicalDomain
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
    (e : input.certified.detectedMultiCenterMolecule.Aut) (mirror : Bool) :
    GeneralRigidLocalSignCorrespondence input cfg c root e mirror := by
  intro rootFixed d t u d_ne_root image_ne_root d_notTwin image_notTwin tRoot uRoot
    tCurrent uCurrent stateRel
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
    exists_physicalFrameAndCalibration_of_physicalGeneralRigidCenter input singleBonded acyclic
      m rfl cfg d t tCurrent calibratedD
  obtain ⟨frameG, alphaG, pointAtG, frameComputedG, matchG, spatialG, _observedG,
    calibrationGNonempty⟩ :=
    exists_physicalFrameAndCalibration_of_physicalGeneralRigidCenter input singleBonded acyclic
      m rfl cfg (m.centerPerm e d) u uCurrent calibratedImage
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
  simpa [ActualLocalSignLaw] using key.mp stateRel

/-! ## Physical slot indices from atom images -/




theorem ligandPermAt_eq_of_ligandAtomAt_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (e : m.Aut) (c : m.Center) (i j : Fin 4)
    (centerFixed : m.centerPerm e c = c)
    (ligandMaps : (e : Equiv.Perm V) (m.ligandAtomAt c i) = m.ligandAtomAt c j) :
    m.ligandPermAt e c i = j := by
  apply m.ligandAtomAt_injective c
  have h := m.ligandAtomAt_ligandPermAt (e := e) (c := c) i
  rw [centerFixed] at h
  rw [h, ligandMaps]

/-! ## The central physical transport theorem -/





















theorem actualGeneralReaderPhysicalBranchTransport
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (i j : Fin 4) (hij : i ≠ j)
    (localSign : ∀ (e : input.certified.detectedMultiCenterMolecule.Aut) (mirror : Bool),
      GeneralRigidLocalSignCorrespondence input cfg c (topTarget input c).1.root e mirror)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (tL tR : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input))
    (sourceL : tL.source = frame.cursorAt (alpha.symm i))
    (sourceR : tR.source = frame.cursorAt (alpha.symm j))
    (realizesL : LocalizedCumulativeTreeRealizes input.certified
      (dependencyReader input c) tL)
    (realizesR : LocalizedCumulativeTreeRealizes input.certified
      (dependencyReader input c) tR)
    (hshape : LocalizedCumulativeDecoratedTree.shape tL =
      LocalizedCumulativeDecoratedTree.shape tR)
    (mirror : Bool)
    (labels : ∀ (path : List Nat)
        (nodeL nodeR : LocalizedCumulativeDecoratedTree input.certified
          (LocalizedUniversalReference.carrierFuel input)),
      subtreeAt? tL path = some nodeL →
        subtreeAt? tR path = some nodeR →
          nodeR.label = labelMirror mirror nodeL.label) :
    RootedTetrahedralBranchSymmetry.BranchTransport
      input.certified.detectedMultiCenterMolecule cfg c i j mirror := by
  classical
  let m : MultiCenterMolecule input.certified.Atom := input.certified.detectedMultiCenterMolecule
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input :=
    globalCarrierFuel_adequate input
  have targetCurrent : (topTarget input c).1.node.current? = some c.1 :=
    topTarget_current input c
  have targetAddress : (topTarget input c).1.address = [] :=
    topTarget_address input c
  have hcu : input.certified.moleculeGraph.Adj c.1 (m.ligandAtomAt c i) :=
    m.ligandAtomAt_adj c i
  have hcv : input.certified.moleculeGraph.Adj c.1 (m.ligandAtomAt c j) :=
    m.ligandAtomAt_adj c j
  have huv : m.ligandAtomAt c i ≠ m.ligandAtomAt c j :=
    fun h => hij (m.ligandAtomAt_injective c h)
  have presentL : frame.cursorAt (alpha.symm i) ∈ frame.cursors :=
    List.get_mem frame.cursors _
  have presentR : frame.cursorAt (alpha.symm j) ∈ frame.cursors :=
    List.get_mem frame.cursors _
  have previousEqL : tL.source.previous? = some (topTarget input c) := by
    rw [sourceL]
    exact input.certified.localizedOccurrenceFourLigandFrame_cursor_previous
      (topTarget input c) frame frameComputed (frame.cursorAt (alpha.symm i)) presentL
  have validL : input.certified.LocalizedRerootCursorValid tL.source := by
    rw [sourceL]
    exact input.certified.localizedOccurrenceFourLigandFrame_cursor_valid
      (topTarget input c) frame frameComputed (frame.cursorAt (alpha.symm i)) presentL
  have sameRootL : tL.source.occurrence.1.root = (topTarget input c).1.root := by
    rw [sourceL]
    exact input.certified.localizedOccurrenceFourLigandFrame_cursor_root
      (topTarget input c) frame frameComputed (frame.cursorAt (alpha.symm i)) presentL
  have previousEqR : tR.source.previous? = some (topTarget input c) := by
    rw [sourceR]
    exact input.certified.localizedOccurrenceFourLigandFrame_cursor_previous
      (topTarget input c) frame frameComputed (frame.cursorAt (alpha.symm j)) presentR
  have validR : input.certified.LocalizedRerootCursorValid tR.source := by
    rw [sourceR]
    exact input.certified.localizedOccurrenceFourLigandFrame_cursor_valid
      (topTarget input c) frame frameComputed (frame.cursorAt (alpha.symm j)) presentR
  have sameRootR : tR.source.occurrence.1.root = (topTarget input c).1.root := by
    rw [sourceR]
    exact input.certified.localizedOccurrenceFourLigandFrame_cursor_root
      (topTarget input c) frame frameComputed (frame.cursorAt (alpha.symm j)) presentR
  have oObservedL : tL.source.occurrence.1.node.current? = some (m.ligandAtomAt c i) := by
    rw [sourceL]
    have h := slotSpec (alpha.symm i)
    rw [show alpha (alpha.symm i) = i from Equiv.apply_symm_apply alpha i] at h
    exact h
  have oObservedR : tR.source.occurrence.1.node.current? = some (m.ligandAtomAt c j) := by
    rw [sourceR]
    have h := slotSpec (alpha.symm j)
    rw [show alpha (alpha.symm j) = j from Equiv.apply_symm_apply alpha j] at h
    exact h
  let φ : AcyclicCutBranchAutomorphism.RootedCutBranchIso input.certified.moleculeGraph
      c.1 (m.ligandAtomAt c i) (m.ligandAtomAt c j) :=
    rootedCutBranchIso_of_shapeMatch (input := input.certified)
      (carrierFuel := LocalizedUniversalReference.carrierFuel input)
      (singleBonded := singleBonded) (acyclic := acyclic)
      enough hshape realizesL realizesR previousEqL validL sameRootL
      previousEqR validR sameRootR oObservedL targetCurrent oObservedR targetCurrent hcu hcv
  let e : m.Aut :=
    AcyclicCutBranchAutomorphism.detectedCutBranchSwapAut input.certified.moleculeGraph c.1
      (m.ligandAtomAt c i) (m.ligandAtomAt c j) acyclic hcu hcv huv singleBonded charge φ
  have physicalFix : (e : Equiv.Perm input.certified.Atom) c.1 = c.1 := by
    have h := AcyclicCutBranchAutomorphism.detectedCutBranchSwapAut_apply_center
      input.certified.moleculeGraph c.1 (m.ligandAtomAt c i) (m.ligandAtomAt c j)
      acyclic hcu hcv huv singleBonded charge φ
    simpa [e] using h
  have rootFixed : (e : Equiv.Perm input.certified.Atom) (topTarget input c).1.root =
      (topTarget input c).1.root := by
    rw [topTarget_root input c]
    exact physicalFix
  have centerFixed : m.centerPerm e c = c :=
    (RootedTetrahedralBranchSymmetry.centerPerm_eq_iff m e c).mpr physicalFix
  have physicalImage : (e : Equiv.Perm input.certified.Atom) (m.ligandAtomAt c i) =
      m.ligandAtomAt c j := by
    have h := AcyclicCutBranchAutomorphism.cutBranchSwap_apply_left
      input.certified.moleculeGraph c.1 (m.ligandAtomAt c i) (m.ligandAtomAt c j)
      acyclic hcu hcv huv φ
    simpa [e, AcyclicCutBranchAutomorphism.detectedCutBranchSwapAut_apply] using h
  refine (RootedBranchTerminalTwinCompletion.branchTransport_iff_orientationAtNonTwinCenters
    m cfg c i j mirror).mpr ⟨e, centerFixed, ?_, ?_⟩
  · exact ligandPermAt_eq_of_ligandAtomAt_eq m e c i j centerFixed physicalImage
  · intro d branch notTwin
    have hd : d.1 ∈ AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph
        c.1 (m.ligandAtomAt c i) :=
      (AcyclicCutBranchAutomorphism.ligandBranchReaches_iff_cutBranchReaches m c i d.1).mp branch
    obtain ⟨p, pAtom⟩ := exists_position_of_mem_cutBranch (input := input.certified)
      (carrierFuel := LocalizedUniversalReference.carrierFuel input)
      (read := dependencyReader input c) (tree := tL)
      (oAtom := m.ligandAtomAt c i) (pAtom := c.1) (w := d.1)
      singleBonded acyclic enough realizesL (topTarget input c) previousEqL validL sameRootL
      oObservedL targetCurrent hcu hd
    let q : Position tR := shapePositionEquiv hshape p
    have subtreeR : subtreeAt? tR p.val = some (positionNode q) := by
      have h := positionNode_spec q
      simpa [q] using h
    have labelL : (positionNode p).label = dependencyReader input c (positionSource p) :=
      positionNode_label_eq_read realizesL p
    have labelR : (positionNode q).label = dependencyReader input c (positionSource q) :=
      positionNode_label_eq_read realizesR q
    have labelRel : (positionNode q).label = labelMirror mirror (positionNode p).label :=
      labels p.val (positionNode p) (positionNode q) (positionNode_spec p) subtreeR
    have hswap : (e : Equiv.Perm input.certified.Atom)
          (positionAtom singleBonded acyclic p) =
        positionAtom singleBonded acyclic q := by
      have h := rootedCutBranchIso_of_shapeMatch_swap_apply (input := input.certified)
        (carrierFuel := LocalizedUniversalReference.carrierFuel input)
        (singleBonded := singleBonded) (acyclic := acyclic)
        (readL := dependencyReader input c) (readR := dependencyReader input c)
        (tL := tL) (tR := tR) (previousL := topTarget input c) (previousR := topTarget input c)
        enough hshape realizesL realizesR previousEqL validL sameRootL
        previousEqR validR sameRootR oObservedL targetCurrent oObservedR targetCurrent
        hcu hcv acyclic huv singleBonded charge p
      simpa [e, q, AcyclicCutBranchAutomorphism.detectedCutBranchSwapAut_apply] using h
    have qAtom : positionAtom singleBonded acyclic q = (m.centerPerm e d).1 := by
      rw [← hswap, pAtom]
      rfl
    have pCurrent : (positionSource p).occurrence.1.node.current? = some d.1 := by
      have h := positionAtom_spec singleBonded acyclic p
      rw [pAtom] at h
      exact h
    have qCurrent : (positionSource q).occurrence.1.node.current? =
        some (m.centerPerm e d).1 := by
      have h := positionAtom_spec singleBonded acyclic q
      rw [qAtom] at h
      exact h
    have reachable : input.certified.ActualChildReachable tL.source (positionSource p) :=
      actualChildReachable_positionSource realizesL p
    have reachableStart : input.certified.ActualChildReachable
        (frame.cursorAt (alpha.symm i)) (positionSource p) := by
      rw [sourceL] at reachable
      exact reachable
    have firstChild : frame.cursorAt (alpha.symm i) ∈
        input.certified.executableLocalizedRerootChildren
          ({ occurrence := topTarget input c, previous? := none } :
            input.certified.LocalizedRerootCursor
              (LocalizedUniversalReference.carrierFuel input)) :=
      ActualReaderPhysicalBranchInverse.mem_executableLocalizedRerootChildren_of_frame
        input.certified (topTarget input c) frame frameComputed
        (frame.cursorAt (alpha.symm i)) presentL
    have firstDeeper : (topTarget input c).1.address.length <
        (frame.cursorAt (alpha.symm i)).occurrence.1.address.length :=
      ActualReaderPhysicalBranchInverse.frame_cursor_strictlyDeeper_of_target_address_nil
        input.certified (topTarget input c) frame frameComputed targetAddress
        (frame.cursorAt (alpha.symm i)) presentL
    have readEqL : dependencyReader input c (positionSource p) =
        LocalizedUniversalReference.referenceState input (positionSource p).occurrence := by
      have h := outward_reachable_dependencyLabel_eq_state input.certified (topTarget input c)
        (LocalizedUniversalReference.referenceState input)
        (frame.cursorAt (alpha.symm i)) (positionSource p) firstChild firstDeeper reachableStart
      simpa [dependencyReader, ActualReaderPhysicalBranchInverse.dependencyReader] using h
    have readEqR : dependencyReader input c (positionSource q) =
        LocalizedUniversalReference.referenceState input (positionSource q).occurrence := by
      have reachableR : input.certified.ActualChildReachable tR.source (positionSource q) :=
        actualChildReachable_positionSource realizesR q
      have reachableStartR : input.certified.ActualChildReachable
          (frame.cursorAt (alpha.symm j)) (positionSource q) := by
        rw [sourceR] at reachableR
        exact reachableR
      have firstChildR : frame.cursorAt (alpha.symm j) ∈
          input.certified.executableLocalizedRerootChildren
            ({ occurrence := topTarget input c, previous? := none } :
              input.certified.LocalizedRerootCursor
                (LocalizedUniversalReference.carrierFuel input)) :=
        ActualReaderPhysicalBranchInverse.mem_executableLocalizedRerootChildren_of_frame
          input.certified (topTarget input c) frame frameComputed
          (frame.cursorAt (alpha.symm j)) presentR
      have firstDeeperR : (topTarget input c).1.address.length <
          (frame.cursorAt (alpha.symm j)).occurrence.1.address.length :=
        ActualReaderPhysicalBranchInverse.frame_cursor_strictlyDeeper_of_target_address_nil
          input.certified (topTarget input c) frame frameComputed targetAddress
          (frame.cursorAt (alpha.symm j)) presentR
      have h := outward_reachable_dependencyLabel_eq_state input.certified (topTarget input c)
        (LocalizedUniversalReference.referenceState input)
        (frame.cursorAt (alpha.symm j)) (positionSource q) firstChildR firstDeeperR reachableStartR
      simpa [dependencyReader, ActualReaderPhysicalBranchInverse.dependencyReader] using h
    have stateRel : LocalizedUniversalReference.referenceState input (positionSource q).occurrence =
        (if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id)
          (LocalizedUniversalReference.referenceState input (positionSource p).occurrence) := by
      calc LocalizedUniversalReference.referenceState input (positionSource q).occurrence
          = dependencyReader input c (positionSource q) := readEqR.symm
        _ = labelMirror mirror (dependencyReader input c (positionSource p)) := by
              rw [← labelR, ← labelL]
              exact labelRel
        _ = (if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id)
              (LocalizedUniversalReference.referenceState input (positionSource p).occurrence) := by
              simp only [labelMirror_eq_if, readEqL]
              cases mirror <;> rfl
    have d_ne_root : d ≠ c := by
      intro hEq
      exact RootedBranchTerminalTwinCompletion.ligandBranchReaches_ne_root m c i branch
        (congrArg Subtype.val hEq)
    have image_ne_root : m.centerPerm e d ≠ c := by
      intro hEq
      have hval : (e : Equiv.Perm input.certified.Atom) d.1 = c.1 :=
        congrArg Subtype.val hEq
      have hdEq : d.1 = c.1 := (e : Equiv.Perm input.certified.Atom).injective
        (hval.trans physicalFix.symm)
      exact d_ne_root (Subtype.ext hdEq)
    have d_notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified m d :=
      fun h => notTwin
        ((actualPhysicalTerminalTwinCenter_iff_hasTerminalTwins input.certified m d).mp h)
    have image_notTwin :
        ¬ ActualPhysicalTerminalTwinCenter input.certified m (m.centerPerm e d) :=
      fun h => d_notTwin
        ((actualPhysicalTerminalTwinCenter_centerPerm_iff input.certified m e d).mp h)
    have positionRootL : (positionSource p).occurrence.1.root = (topTarget input c).1.root :=
      (positionSource_root_eq_of_realized realizesL p).trans sameRootL
    have positionRootR : (positionSource q).occurrence.1.root = (topTarget input c).1.root :=
      (positionSource_root_eq_of_realized realizesR q).trans sameRootR
    exact localSign e mirror rootFixed d (positionSource p).occurrence
      (positionSource q).occurrence d_ne_root image_ne_root d_notTwin image_notTwin
      positionRootL positionRootR pCurrent qCurrent stateRel







theorem actualGeneralReaderPhysicalBranchTransport_of_physicalDomain
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
    (i j : Fin 4) (hij : i ≠ j)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (tL tR : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input))
    (sourceL : tL.source = frame.cursorAt (alpha.symm i))
    (sourceR : tR.source = frame.cursorAt (alpha.symm j))
    (realizesL : LocalizedCumulativeTreeRealizes input.certified
      (dependencyReader input c) tL)
    (realizesR : LocalizedCumulativeTreeRealizes input.certified
      (dependencyReader input c) tR)
    (hshape : LocalizedCumulativeDecoratedTree.shape tL =
      LocalizedCumulativeDecoratedTree.shape tR)
    (mirror : Bool)
    (labels : ∀ (path : List Nat)
        (nodeL nodeR : LocalizedCumulativeDecoratedTree input.certified
          (LocalizedUniversalReference.carrierFuel input)),
      subtreeAt? tL path = some nodeL →
        subtreeAt? tR path = some nodeR →
          nodeR.label = labelMirror mirror nodeL.label) :
    RootedTetrahedralBranchSymmetry.BranchTransport
      input.certified.detectedMultiCenterMolecule cfg c i j mirror :=
  actualGeneralReaderPhysicalBranchTransport input noDouble singleBonded acyclic charge cfg c i j
    hij
    (fun e mirror =>
      generalRigidLocalSignCorrespondence_of_physicalDomain input noDouble singleBonded acyclic
        charge cfg c domain (topTarget input c).1.root e mirror)
    frame alpha frameComputed slotSpec tL tR sourceL sourceR realizesL realizesR hshape mirror labels

/-! ## Public kernel guards -/

assert_kernel_only TetraStereo.OneCenter.ActualGeneralRigidPhysicalBranchInverse.topTarget
assert_kernel_only TetraStereo.OneCenter.ActualGeneralRigidPhysicalBranchInverse.dependencyReader
assert_kernel_only TetraStereo.OneCenter.ActualGeneralRigidPhysicalBranchInverse.topTarget_current
assert_kernel_only TetraStereo.OneCenter.ActualGeneralRigidPhysicalBranchInverse.topTarget_address
assert_kernel_only TetraStereo.OneCenter.ActualGeneralRigidPhysicalBranchInverse.topTarget_root
assert_kernel_only
  TetraStereo.OneCenter.ActualGeneralRigidPhysicalBranchInverse.exists_physicalFrameAndCalibration_of_physicalGeneralRigidCenter
assert_kernel_only
  TetraStereo.OneCenter.ActualGeneralRigidPhysicalBranchInverse.generalRigidCalibratedCenter_of_canonicalDomain
assert_kernel_only
  TetraStereo.OneCenter.ActualGeneralRigidPhysicalBranchInverse.exists_generalRigidPositiveReadback_of_canonicalDomain
assert_kernel_only
  TetraStereo.OneCenter.ActualGeneralRigidPhysicalBranchInverse.exists_chiral_referenceState_of_canonicalDomain
assert_kernel_only
  TetraStereo.OneCenter.ActualGeneralRigidPhysicalBranchInverse.constitutionallyRigidGraphAt_of_canonicalDomain
assert_kernel_only
  TetraStereo.OneCenter.ActualGeneralRigidPhysicalBranchInverse.GeneralRigidLocalSignCorrespondence
assert_kernel_only
  TetraStereo.OneCenter.ActualGeneralRigidPhysicalBranchInverse.generalRigidLocalSignCorrespondence_of_referenceState_iff
assert_kernel_only
  TetraStereo.OneCenter.ActualGeneralRigidPhysicalBranchInverse.generalRigidLocalSignCorrespondence_of_physicalDomain
assert_kernel_only
  TetraStereo.OneCenter.ActualGeneralRigidPhysicalBranchInverse.ligandPermAt_eq_of_ligandAtomAt_eq
assert_kernel_only
  TetraStereo.OneCenter.ActualGeneralRigidPhysicalBranchInverse.actualGeneralReaderPhysicalBranchTransport
assert_kernel_only
  TetraStereo.OneCenter.ActualGeneralRigidPhysicalBranchInverse.actualGeneralReaderPhysicalBranchTransport_of_physicalDomain

end ActualGeneralRigidPhysicalBranchInverse

end TetraStereo.OneCenter
