import TetraStereo.OneCenter.LocalizedPhysicalCalibratedRootReader
import TetraStereo.OneCenter.LocalizedActualRigidFrameCompleteness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false





































namespace TetraStereo
namespace OneCenter
namespace CertifiedLocalizedCIPInput

open TetraStereo.OneCenter
open TerminalTwinConfigurationGauge
open RootedTetrahedralBranchSymmetry
open AcyclicCutBranchAutomorphism

/-! ## General rigid calibrated center data -/








def ActualGeneralRigidCalibratedCenter
    (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (center : input.TetrahedralCenter) : Prop :=
  ConstitutionallyRigid input.detectedMultiCenterMolecule ⟨center.1, center.2⟩ ∧
    ∃ pointAt : Fin 4 → CartesianPoint3,
      (∀ i, input.spatialPointAt? (input.canonicalLigandAtom center i) = some (pointAt i)) ∧
        CartesianPoint3.orientedVolume
            (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) ≠ 0 ∧
          rationalVolumeSign
            (CartesianPoint3.orientedVolume
              (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3)) =
            input.detectedMultiCenterMolecule.configurationSign cfg ⟨center.1, center.2⟩




theorem constitutionallyRigidGraphAt_of_generalRigidCalibratedCenter
    {input : CertifiedLocalizedCIPInput}
    {cfg : input.detectedMultiCenterMolecule.Configuration}
    {center : input.TetrahedralCenter}
    (calibrated : ActualGeneralRigidCalibratedCenter input cfg center) :
    ConstitutionallyRigidGraphAt input.moleculeGraph center.1 :=
  constitutionallyRigidGraphAt_of_constitutionallyRigid_detected input
    ⟨center.1, center.2⟩ calibrated.1

/-- **The global general rigid physical domain.**  One canonical detected physical molecule, one
shared configuration `cfg`, one physical root candidate `root`.  The graph equation and the exact
degree-four center inventory are the detected ones (both definitional), and every non-root
candidate is a physical terminal twin or a general rigid calibrated center.

The root is deliberately unconstrained.  No frame success, slot permutation, geometry, label,
key-table interface, reader covariance or physical automorphism sign law is a field. -/
structure ActualGeneralRigidGlobalPhysicalDomain
    (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (root : input.TetrahedralCenter) : Prop where
  /-- The physical molecule has exactly the certified input graph. -/
  graphEq : input.detectedMultiCenterMolecule.mol = input.moleculeGraph
  /-- The center inventory is exactly the detected degree-four candidate set. -/
  centersEq : input.detectedMultiCenterMolecule.centers = input.tetrahedralCenterSet
  /-- Every non-root candidate is a physical terminal twin or a general rigid calibrated center. -/
  centerCase : ∀ center : input.TetrahedralCenter, center ≠ root →
    ActualPhysicalTerminalTwinCenter input input.detectedMultiCenterMolecule
        ⟨center.1, center.2⟩ ∨
      ActualGeneralRigidCalibratedCenter input cfg center

/-- Constructor of the global general rigid domain from its only non-definitional field.  The graph
and inventory fields are the detected ones and hold definitionally. -/
def actualGeneralRigidGlobalPhysicalDomain_of_centerCase
    (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (root : input.TetrahedralCenter)
    (centerCase : ∀ center : input.TetrahedralCenter, center ≠ root →
      ActualPhysicalTerminalTwinCenter input input.detectedMultiCenterMolecule
          ⟨center.1, center.2⟩ ∨
        ActualGeneralRigidCalibratedCenter input cfg center) :
    ActualGeneralRigidGlobalPhysicalDomain input cfg root :=
  { graphEq := rfl
    centersEq := rfl
    centerCase := centerCase }


abbrev GeneralRigidCalibratedRootDomain
    (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (root : input.TetrahedralCenter) : Prop :=
  ActualGeneralRigidGlobalPhysicalDomain input cfg root

/-- In the global domain, a non-root candidate that is not a physical terminal twin is general
rigid calibrated. -/
theorem actualGeneralRigidCalibratedCenter_of_globalDomain
    {input : CertifiedLocalizedCIPInput}
    {cfg : input.detectedMultiCenterMolecule.Configuration}
    {root : input.TetrahedralCenter}
    (domain : ActualGeneralRigidGlobalPhysicalDomain input cfg root)
    {center : input.TetrahedralCenter}
    (center_ne_root : center ≠ root)
    (notTwin : ¬ ActualPhysicalTerminalTwinCenter input input.detectedMultiCenterMolecule
      ⟨center.1, center.2⟩) :
    ActualGeneralRigidCalibratedCenter input cfg center := by
  rcases domain.centerCase center center_ne_root with twin | calibrated
  · exact absurd twin notTwin
  · exact calibrated





theorem false_of_generalRigidCalibratedCenter_and_twin
    {input : CertifiedLocalizedCIPInput}
    {cfg : input.detectedMultiCenterMolecule.Configuration}
    {center : input.TetrahedralCenter}
    (calibrated : ActualGeneralRigidCalibratedCenter input cfg center)
    (twin : ActualPhysicalTerminalTwinCenter input input.detectedMultiCenterMolecule
      ⟨center.1, center.2⟩) :
    False := by
  classical
  obtain ⟨rigid, _pointAt, _observed, _nonzero, _sign⟩ := calibrated
  obtain ⟨a, b, pair⟩ := twin
  have centerFixed :
      input.detectedMultiCenterMolecule.centerPerm pair.swapAut
        ⟨center.1, center.2⟩ = ⟨center.1, center.2⟩ :=
    pair.centerPerm_swapAut_apply ⟨center.1, center.2⟩
  have permEq :
      input.detectedMultiCenterMolecule.ligandPermAt pair.swapAut
        ⟨center.1, center.2⟩ = 1 :=
    rigid pair.swapAut centerFixed
  have swapEq : Equiv.swap pair.twinSlotA pair.twinSlotB = (1 : Equiv.Perm (Fin 4)) := by
    rw [← pair.ligandPermAt_swapAut_center]
    exact permEq
  have slotsEq : pair.twinSlotB = pair.twinSlotA := by
    have image := congrArg (fun e : Equiv.Perm (Fin 4) => e pair.twinSlotA) swapEq
    simpa using image
  exact pair.twinSlotA_ne_twinSlotB slotsEq.symm

/-- A general rigid calibrated center is never a physical terminal twin. -/
theorem actualPhysicalTerminalTwinCenter_false_of_generalRigidCalibrated
    {input : CertifiedLocalizedCIPInput}
    {cfg : input.detectedMultiCenterMolecule.Configuration}
    {center : input.TetrahedralCenter}
    (calibrated : ActualGeneralRigidCalibratedCenter input cfg center) :
    ¬ ActualPhysicalTerminalTwinCenter input input.detectedMultiCenterMolecule
      ⟨center.1, center.2⟩ :=
  fun twin => false_of_generalRigidCalibratedCenter_and_twin calibrated twin

/-! ## Actual frame and physical calibration from one general rigid center -/











theorem exists_frameAndCalibration_of_generalRigidCenter
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (center : input.certified.TetrahedralCenter)
    (target : LocalizedUniversalReference.Occurrence input)
    (targetCurrent : target.1.node.current? = some center.1)
    (calibrated : ActualGeneralRigidCalibratedCenter input.certified cfg center) :
    ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (alpha : Equiv.Perm (Fin 4))
      (pointAt : Fin 4 → CartesianPoint3),
      input.certified.localizedOccurrenceFourLigandFrame? target = some frame ∧
        (∀ i, (frame.cursorAt i).occurrence.1.node.current? =
          some (input.certified.canonicalLigandAtom center (alpha i))) ∧
        (∀ i, input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt i) =
          some (pointAt (alpha i))) ∧
        (∀ i, input.certified.spatialPointAt?
          (input.certified.canonicalLigandAtom center i) = some (pointAt i)) ∧
        Nonempty (PhysicalFrameCalibration input.certified.detectedMultiCenterMolecule
          cfg ⟨center.1, center.2⟩ alpha (fun i => pointAt (alpha i))) := by
  classical
  obtain ⟨_rigid, pointAt, observed, nonzero, signEq⟩ := calibrated
  obtain ⟨frame, frameComputed⟩ :=
    input.certified.exists_localizedOccurrenceFourLigandFrame_of_detectedCenter
      singleBonded acyclic (globalCarrierFuel_adequate input) target targetCurrent
      ⟨center.1, center.2⟩ rfl
  have derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame :=
    input.certified.localizedOccurrenceFourLigandFrame?_sound target frame frameComputed
  have centerReal : input.certified.RealTetrahedralCenterNode target.1.node center :=
    ⟨input.certified.carrierOccurrence_provenance_real singleBonded acyclic target,
      targetCurrent⟩
  obtain ⟨alpha, ligandLink⟩ :=
    exists_ligandPermutation_of_actualFrame input.certified target frame derived center centerReal
      singleBonded acyclic (globalCarrierFuel_adequate input)
  have spatial : ∀ i : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt i) =
        some (pointAt (alpha i)) := by
    intro i
    simp [localizedRerootCursorSpatialPoint?, ligandLink i, observed (alpha i)]
  refine ⟨frame, alpha, pointAt, frameComputed, ligandLink, spatial, observed, ?_⟩
  exact
    ⟨{ physicalPointAt := pointAt
       calibrated := fun _i => rfl
       nondegenerate := nonzero
       sign_eq := signEq }⟩

/-! ## Actual positive reader at a general rigid center -/





def ActualGeneralRigidPositiveReadback
    (input : LocalizedUniversalReference.Input)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (center : input.certified.TetrahedralCenter)
    (target : LocalizedUniversalReference.Occurrence input) : Prop :=
  ∃ (rs : RS) (tracked : TrackedLocalizedLigandOrder)
      (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (alpha : Equiv.Perm (Fin 4)) (pointAt : Fin 4 → CartesianPoint3),
      target.1.node.current? = some center.1 ∧
        ¬ ActualPhysicalTerminalTwinCenter input.certified
            input.certified.detectedMultiCenterMolecule ⟨center.1, center.2⟩ ∧
        ActualGeneralRigidCalibratedCenter input.certified cfg center ∧
        input.certified.localizedOccurrenceFourLigandFrame? target = some frame ∧
        (∀ i, (frame.cursorAt i).occurrence.1.node.current? =
          some (input.certified.canonicalLigandAtom center (alpha i))) ∧
        (∀ i, input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt i) =
          some (pointAt (alpha i))) ∧
        (∀ i, input.certified.spatialPointAt?
          (input.certified.canonicalLigandAtom center i) = some (pointAt i)) ∧
        Nonempty (PhysicalFrameCalibration input.certified.detectedMultiCenterMolecule
          cfg ⟨center.1, center.2⟩ alpha (fun i => pointAt (alpha i))) ∧
        input.certified.localizedOccurrenceRule45TrackedOrder? target
            (input.certified.localizedDependencyView
              (LocalizedUniversalReference.referenceState input) target) frame = some tracked ∧
        tracked.pseudoComparisons = 0 ∧
        LocalizedUniversalReference.referenceState input target = some (.chiral rs) ∧
        rationalVolumeSign
            (CartesianPoint3.orientedVolume
              (pointAt (alpha 0)) (pointAt (alpha 1))
              (pointAt (alpha 2)) (pointAt (alpha 3))) =
          input.certified.detectedMultiCenterMolecule.configurationSign cfg
            ⟨center.1, center.2⟩ * permHandedness alpha








theorem actualGeneralRigidPositiveReadback_of_calibratedCenter
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (center : input.certified.TetrahedralCenter)
    (target : LocalizedUniversalReference.Occurrence input)
    (targetCurrent : target.1.node.current? = some center.1)
    (calibrated : ActualGeneralRigidCalibratedCenter input.certified cfg center) :
    ActualGeneralRigidPositiveReadback input cfg center target := by
  classical
  obtain ⟨frame, alpha, pointAt, frameComputed, ligandLink, spatial, observed,
    calibrationNonempty⟩ :=
    exists_frameAndCalibration_of_generalRigidCenter input singleBonded acyclic cfg center target
      targetCurrent calibrated
  obtain ⟨calibration⟩ := calibrationNonempty
  let pointsAt : Fin 4 → CartesianPoint3 := fun index => pointAt (alpha index)
  have writtenNondegenerate : CartesianPoint3.orientedVolume
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0 :=
    calibration.written_nondegenerate
  have writtenParity :
      AuthoritativeChemicalInput.RationalTetrahedralInputParity
        [pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3]
        (TetraStereo.OneCenter.parityOfVolumeSign
          (TetraStereo.OneCenter.rationalVolumeSign
            (CartesianPoint3.orientedVolume
              (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3)))) :=
    TetraStereo.OneCenter.rationalTetrahedralInputParity_parityOfVolumeSign
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) writtenNondegenerate
  have centerReal : input.certified.RealTetrahedralCenterNode target.1.node center :=
    ⟨input.certified.carrierOccurrence_provenance_real singleBonded acyclic target,
      targetCurrent⟩
  obtain ⟨tracked, trackedComputed, pseudoZero, state⟩ :=
    referenceState_reader_eq_chiral_of_detectedRigid_derived
      (input := input) (noDouble := noDouble) (target := target) (frame := frame)
      (derived := input.certified.localizedOccurrenceFourLigandFrame?_sound target frame
        frameComputed)
      (center := center) (centerReal := centerReal) (rigid := calibrated.1)
      (hacyc := acyclic) (hsimple := singleBonded) (hcharge := hcharge)
      (pointsAt := pointsAt) (spatial := spatial)
      (parity := TetraStereo.OneCenter.parityOfVolumeSign
        (TetraStereo.OneCenter.rationalVolumeSign
          (CartesianPoint3.orientedVolume
            (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3))))
      (writtenParity := writtenParity)
  have signNormalized :
      rationalVolumeSign
          (CartesianPoint3.orientedVolume
            (pointAt (alpha 0)) (pointAt (alpha 1))
            (pointAt (alpha 2)) (pointAt (alpha 3))) =
        input.certified.detectedMultiCenterMolecule.configurationSign cfg
          ⟨center.1, center.2⟩ * permHandedness alpha := by
    simpa [pointsAt] using calibration.sign_eq_configurationSign_mul
  exact ⟨_, tracked, frame, alpha, pointAt, targetCurrent,
    actualPhysicalTerminalTwinCenter_false_of_generalRigidCalibrated calibrated,
    calibrated, frameComputed, ligandLink, spatial, observed, ⟨calibration⟩, trackedComputed,
    pseudoZero, state, signNormalized⟩

/-! ## Exact candidate-center dichotomies -/







theorem actualGeneralRigidCandidateCenter_referenceState_none_iff_twin
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.TetrahedralCenter)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg root)
    (center : input.certified.TetrahedralCenter)
    (center_ne_root : center ≠ root)
    (target : LocalizedUniversalReference.Occurrence input)
    (targetCurrent : target.1.node.current? = some center.1)
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root) :
    LocalizedUniversalReference.referenceState input target = none ↔
      ActualPhysicalTerminalTwinCenter input.certified
        input.certified.detectedMultiCenterMolecule ⟨center.1, center.2⟩ := by
  constructor
  · intro noneEq
    by_contra notTwin
    have calibrated : ActualGeneralRigidCalibratedCenter input.certified cfg center :=
      actualGeneralRigidCalibratedCenter_of_globalDomain domain center_ne_root notTwin
    obtain ⟨_rs, _tracked, _frame, _alpha, _pointAt, _current, _notTwin, _calibrated,
      _frameComputed, _ligandLink, _spatial, _observed, _calibration, _trackedOrder, _pseudo,
      state, _sign⟩ :=
      actualGeneralRigidPositiveReadback_of_calibratedCenter input singleBonded acyclic hcharge
        noDouble cfg center target targetCurrent calibrated
    rw [noneEq] at state
    cases state
  · intro twin
    have currentDetected : target.1.node.current? =
        some (⟨center.1, center.2⟩ :
          input.certified.detectedMultiCenterMolecule.Center).1 := by
      simpa using targetCurrent
    exact referenceState_eq_none_of_globalTwinCenter input singleBonded acyclic noDouble
      input.certified.detectedMultiCenterMolecule rfl ⟨center.1, center.2⟩ target
      currentDetected rootTetrahedral twin

/-- **Exact candidate-center dichotomy: actual positive chiral iff no physical terminal twins.**
At the same non-root candidate center, the generated reference state is an actual uppercase chiral
value exactly when the center is not a physical terminal twin. -/
theorem actualGeneralRigidCandidateCenter_referenceState_chiral_iff_notTwin
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.TetrahedralCenter)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg root)
    (center : input.certified.TetrahedralCenter)
    (center_ne_root : center ≠ root)
    (target : LocalizedUniversalReference.Occurrence input)
    (targetCurrent : target.1.node.current? = some center.1)
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root) :
    (∃ rs : RS, LocalizedUniversalReference.referenceState input target = some (.chiral rs)) ↔
      ¬ ActualPhysicalTerminalTwinCenter input.certified
        input.certified.detectedMultiCenterMolecule ⟨center.1, center.2⟩ := by
  constructor
  · rintro ⟨_rs, someEq⟩ twin
    have currentDetected : target.1.node.current? =
        some (⟨center.1, center.2⟩ :
          input.certified.detectedMultiCenterMolecule.Center).1 := by
      simpa using targetCurrent
    have noneEq := referenceState_eq_none_of_globalTwinCenter input singleBonded acyclic
      noDouble input.certified.detectedMultiCenterMolecule rfl ⟨center.1, center.2⟩ target
      currentDetected rootTetrahedral twin
    rw [noneEq] at someEq
    cases someEq
  · intro notTwin
    have calibrated : ActualGeneralRigidCalibratedCenter input.certified cfg center :=
      actualGeneralRigidCalibratedCenter_of_globalDomain domain center_ne_root notTwin
    obtain ⟨rs, _tracked, _frame, _alpha, _pointAt, _current, _notTwin, _calibrated,
      _frameComputed, _ligandLink, _spatial, _observed, _calibration, _trackedOrder, _pseudo,
      state, _sign⟩ :=
      actualGeneralRigidPositiveReadback_of_calibratedCenter input singleBonded acyclic hcharge
        noDouble cfg center target targetCurrent calibrated
    exact ⟨rs, state⟩

/-! ## Global classification of actual strict dependencies -/

















theorem actualStrictDependency_classification_generalRigid
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.TetrahedralCenter)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg root)
    (topCenter : input.certified.TetrahedralCenter)
    (topAt : topCenter.1 = root.1)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (dependency : input.certified.LocalizedDepthDependency cursor.occurrence
      (input.certified.localizedFinalOccurrence
        (LocalizedUniversalReference.carrierFuel input) topCenter)) :
    (ActualPhysicalNoncandidate input cursor.occurrence ∧
        LocalizedUniversalReference.referenceState input cursor.occurrence = none) ∨
      (ActualPhysicalTerminalTwinLeaves input cursor.occurrence ∧
        LocalizedUniversalReference.referenceState input cursor.occurrence = none) ∨
        (∃ center : input.certified.TetrahedralCenter,
          ActualGeneralRigidPositiveReadback input cfg center cursor.occurrence) := by
  classical
  obtain ⟨currentAtom, currentEq⟩ :=
    input.certified.localizedRerootCursor_current_exists cursor
  have finalRoot : cursor.occurrence.1.root = topCenter.1 := by
    rw [dependency.1]
    exact AuxiliaryContextIntegrity.localizedFinalOccurrence_root input.certified
      (LocalizedUniversalReference.carrierFuel input) topCenter
  have rootTetrahedral :
      input.certified.moleculeGraph.IsTetrahedralCenter cursor.occurrence.1.root := by
    rw [finalRoot]
    exact (input.certified.moleculeGraph.mem_tetrahedralCenterSet topCenter.1).mp topCenter.2
  by_cases candidate : currentAtom ∈ input.certified.detectedMultiCenterMolecule.centers
  · let center : input.certified.TetrahedralCenter := ⟨currentAtom, candidate⟩
    have centerAt : cursor.occurrence.1.node.current? = some center.1 := currentEq
    have center_ne_root : center ≠ root := by
      intro centerEqRoot
      have valueEq : center.1 = root.1 := congrArg Subtype.val centerEqRoot
      have atomEqRoot : currentAtom = root.1 := valueEq
      have atomEqTop : currentAtom = topCenter.1 := atomEqRoot.trans topAt.symm
      have currentTop : cursor.occurrence.1.node.current? = some topCenter.1 := by
        rw [currentEq, atomEqTop]
      exact dependency_current_ne_topAtom_of_finalOccurrence input singleBonded acyclic
        topCenter cursor dependency currentTop
    rcases domain.centerCase center center_ne_root with twin | calibrated
    · have currentDetected : cursor.occurrence.1.node.current? =
          some (⟨center.1, center.2⟩ :
            input.certified.detectedMultiCenterMolecule.Center).1 := by
        simpa using centerAt
      exact Or.inr (Or.inl
        ⟨actualPhysicalTerminalTwinLeaves_of_globalTwinCenter input
            input.certified.detectedMultiCenterMolecule rfl ⟨center.1, center.2⟩
            cursor.occurrence currentDetected twin,
          referenceState_eq_none_of_globalTwinCenter input singleBonded acyclic noDouble
            input.certified.detectedMultiCenterMolecule rfl ⟨center.1, center.2⟩
            cursor.occurrence currentDetected rootTetrahedral twin⟩)
    · exact Or.inr (Or.inr ⟨center,
        actualGeneralRigidPositiveReadback_of_calibratedCenter input singleBonded acyclic hcharge
          noDouble cfg center cursor.occurrence centerAt calibrated⟩)
  · have notCandidate : currentAtom ∉ input.certified.tetrahedralCenterSet :=
      fun detected => candidate detected
    have noncandidate : ActualPhysicalNoncandidate input cursor.occurrence :=
      ⟨currentAtom, currentEq, notCandidate⟩
    exact Or.inl
      ⟨noncandidate,
        referenceState_eq_none_of_actualPhysicalNoncandidate input noDouble
          cursor.occurrence noncandidate⟩

/-- **Reader-level classification of actual strict dependencies.**  Every actual strict dependency
of the top final occurrence reads either `none` or an actual uppercase chiral label.  This is the
reader projection of the global general-rigid classification and the stable consumer signature. -/
theorem actualStrictDependency_referenceState_none_or_chiral_generalRigid
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.TetrahedralCenter)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg root)
    (topCenter : input.certified.TetrahedralCenter)
    (topAt : topCenter.1 = root.1)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (dependency : input.certified.LocalizedDepthDependency cursor.occurrence
      (input.certified.localizedFinalOccurrence
        (LocalizedUniversalReference.carrierFuel input) topCenter)) :
    LocalizedUniversalReference.referenceState input cursor.occurrence = none ∨
      ∃ rs : RS,
        LocalizedUniversalReference.referenceState input cursor.occurrence =
          some (.chiral rs) := by
  rcases actualStrictDependency_classification_generalRigid input singleBonded acyclic hcharge
    noDouble cfg root domain topCenter topAt cursor dependency with
    ⟨_noncandidate, noneEq⟩ | ⟨_twins, noneEq⟩ | ⟨_center, positive⟩
  · exact Or.inl noneEq
  · exact Or.inl noneEq
  · obtain ⟨rs, _tracked, _frame, _alpha, _pointAt, _current, _notTwin, _calibrated,
      _frameComputed, _ligandLink, _spatial, _observed, _calibration, _trackedOrder, _pseudo,
      state, _sign⟩ := positive
    exact Or.inr ⟨rs, state⟩




theorem actualStrictDependency_referenceState_sparseLabel_generalRigid
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.TetrahedralCenter)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg root)
    (topCenter : input.certified.TetrahedralCenter)
    (topAt : topCenter.1 = root.1)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (dependency : input.certified.LocalizedDepthDependency cursor.occurrence
      (input.certified.localizedFinalOccurrence
        (LocalizedUniversalReference.carrierFuel input) topCenter)) :
    LocalizedRule4bSparseLabel
      (LocalizedUniversalReference.referenceState input cursor.occurrence) := by
  rcases actualStrictDependency_referenceState_none_or_chiral_generalRigid input singleBonded
    acyclic hcharge noDouble cfg root domain topCenter topAt cursor dependency with
    noneEq | ⟨rs, someEq⟩
  · exact Or.inl noneEq
  · exact Or.inr ⟨rs, someEq⟩

/-! ## Public kernel guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualGeneralRigidCalibratedCenter
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.constitutionallyRigidGraphAt_of_generalRigidCalibratedCenter
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualGeneralRigidGlobalPhysicalDomain
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualGeneralRigidGlobalPhysicalDomain_of_centerCase
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.GeneralRigidCalibratedRootDomain
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualGeneralRigidCalibratedCenter_of_globalDomain
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.false_of_generalRigidCalibratedCenter_and_twin
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualPhysicalTerminalTwinCenter_false_of_generalRigidCalibrated
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_frameAndCalibration_of_generalRigidCenter
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualGeneralRigidPositiveReadback
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualGeneralRigidPositiveReadback_of_calibratedCenter
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualGeneralRigidCandidateCenter_referenceState_none_iff_twin
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualGeneralRigidCandidateCenter_referenceState_chiral_iff_notTwin
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualStrictDependency_classification_generalRigid
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualStrictDependency_referenceState_none_or_chiral_generalRigid
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualStrictDependency_referenceState_sparseLabel_generalRigid

end CertifiedLocalizedCIPInput

end OneCenter
end TetraStereo
