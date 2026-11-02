import TetraStereo.OneCenter.LocalizedGeneralRigidLabelCovariance
import TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalBranchInverse
import TetraStereo.OneCenter.LocalizedPhysicalBranchKeyTransport
import TetraStereo.OneCenter.LocalizedPhysicalCompoundForwardTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open AcyclicCutBranchAutomorphism
open RootedTetrahedralBranchSymmetry
open ActualGeneralRigidPhysicalBranchInverse
































theorem localizedGeneralRigidPhysicalTerminalTwinCenter_false_of_physicalCalibrated
    {input : CertifiedLocalizedCIPInput}
    {m : MultiCenterMolecule input.Atom}
    {cfg : m.Configuration} {center : m.Center}
    (calibrated : ActualPhysicalGeneralRigidCalibratedCenter input m cfg center) :
    ¬ ActualPhysicalTerminalTwinCenter input m center := by
  classical
  obtain ⟨rigid, _pointAt, _observed, _nonzero, _sign⟩ := calibrated
  rintro ⟨a, b, pair⟩
  have centerFixed : m.centerPerm pair.swapAut center = center :=
    pair.centerPerm_swapAut_apply center
  have permEq : m.ligandPermAt pair.swapAut center = 1 := rigid pair.swapAut centerFixed
  have swapEq : Equiv.swap pair.twinSlotA pair.twinSlotB = (1 : Equiv.Perm (Fin 4)) := by
    rw [← pair.ligandPermAt_swapAut_center]
    exact permEq
  have slotsEq : pair.twinSlotB = pair.twinSlotA := by
    have image := congrArg (fun e : Equiv.Perm (Fin 4) => e pair.twinSlotA) swapEq
    simpa using image
  exact pair.twinSlotA_ne_twinSlotB slotsEq.symm










theorem localizedGeneralRigidPhysicalBranchRelation_referenceState_globalDomain
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (e : input.certified.detectedMultiCenterMolecule.Aut)
    (mirror : Bool) (i : Fin 4)
    (centerFixed :
      input.certified.detectedMultiCenterMolecule.centerPerm e c = c)
    (signLaw : ∀ d : input.certified.detectedMultiCenterMolecule.Center,
      LigandBranchReaches input.certified.detectedMultiCenterMolecule c i d.1 →
      input.certified.detectedMultiCenterMolecule.configurationSign cfg d *
        permHandedness
          (input.certified.detectedMultiCenterMolecule.ligandPermAt e d) =
        (if mirror then -1 else 1) *
          input.certified.detectedMultiCenterMolecule.configurationSign cfg
            (input.certified.detectedMultiCenterMolecule.centerPerm e d))
    (topCenter : input.certified.TetrahedralCenter)
    (topAt : topCenter.1 = c.1)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg ⟨topCenter.1, topCenter.2⟩)
    {startL startR : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input)}
    (branchAtLeft : ∀ (x : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input)) (a : input.certified.Atom),
      input.certified.ActualChildReachable startL x →
      x.occurrence.1.node.current? = some a →
      LigandBranchReaches input.certified.detectedMultiCenterMolecule c i a)
    {x y : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input)}
    (related : LocalizedPhysicalBranchRelation input.certified
      (graphAutOfMultiCenterAut input.certified
        input.certified.detectedMultiCenterMolecule rfl e)
      c.1 startL startR x y)
    (xDependency : input.certified.LocalizedDepthDependency x.occurrence
      (input.certified.localizedFinalOccurrence
        (LocalizedUniversalReference.carrierFuel input) topCenter))
    (yDependency : input.certified.LocalizedDepthDependency y.occurrence
      (input.certified.localizedFinalOccurrence
        (LocalizedUniversalReference.carrierFuel input) topCenter)) :
    LocalizedUniversalReference.referenceState input y.occurrence =
      (if mirror then reflectUppercaseOptionalLabel else id)
        (LocalizedUniversalReference.referenceState input x.occurrence) := by
  classical
  let m : MultiCenterMolecule input.certified.Atom :=
    input.certified.detectedMultiCenterMolecule
  let root : m.Center := ⟨topCenter.1, topCenter.2⟩
  have coverage : m.centers = input.certified.tetrahedralCenterSet := rfl
  obtain ⟨a, xCurrent⟩ := input.certified.occurrence_current_exists x.occurrence
  obtain ⟨b, yCurrent⟩ := input.certified.occurrence_current_exists y.occurrence
  have bEq : b = (e : Equiv.Perm input.certified.Atom) a := by
    simpa [m, graphAutOfMultiCenterAut] using related.1.current_maps xCurrent yCurrent
  have rootX : x.occurrence.1.root = c.1 := by
    rw [xDependency.1,
      AuxiliaryContextIntegrity.localizedFinalOccurrence_root input.certified
        (LocalizedUniversalReference.carrierFuel input) topCenter,
      topAt]
  have rootY : y.occurrence.1.root = c.1 := by
    rw [yDependency.1,
      AuxiliaryContextIntegrity.localizedFinalOccurrence_root input.certified
        (LocalizedUniversalReference.carrierFuel input) topCenter,
      topAt]
  have rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter c.1 :=
    (input.certified.moleculeGraph.mem_tetrahedralCenterSet c.1).mp
      (mem_tetrahedralCenterSet_of_center coverage c)
  have xRootTetrahedral :
      input.certified.moleculeGraph.IsTetrahedralCenter x.occurrence.1.root := by
    rw [rootX]
    exact rootTetrahedral
  have yRootTetrahedral :
      input.certified.moleculeGraph.IsTetrahedralCenter y.occurrence.1.root := by
    rw [rootY]
    exact rootTetrahedral
  by_cases candidate : a ∈ m.centers
  · let d : m.Center := ⟨a, candidate⟩
    have branchMem : LigandBranchReaches m c i d.1 :=
      branchAtLeft x a related.2.1 xCurrent
    have d_ne_root : d ≠ root := by
      intro h
      have valEq : a = c.1 := (congrArg Subtype.val h).trans topAt
      exact (ligandBranchReaches_ne_center m c i branchMem) valEq
    have yCurrentImage : y.occurrence.1.node.current? = some (m.centerPerm e d).1 := by
      rw [yCurrent]
      show some b = some ((e : Equiv.Perm input.certified.Atom) a)
      exact congrArg some bEq
    rcases domain.centerCase d d_ne_root with twinD | calibratedD
    · -- Physical terminal twin at the source center: both generated readers are `none`.
      have twinImage :
          ActualPhysicalTerminalTwinCenter input.certified m (m.centerPerm e d) :=
        (actualPhysicalTerminalTwinCenter_centerPerm_iff input.certified m e d).mpr
          twinD
      have xNone :=
        referenceState_eq_none_of_globalTwinCenter input singleBonded acyclic noDouble m
          rfl d x.occurrence xCurrent xRootTetrahedral twinD
      have yNone :=
        referenceState_eq_none_of_globalTwinCenter input singleBonded acyclic noDouble m
          rfl (m.centerPerm e d) y.occurrence yCurrentImage yRootTetrahedral twinImage
      rw [xNone, yNone]
      cases mirror <;>
        simp [CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel]
    · -- General rigid calibrated center: actual positive reader covariance.
      have calibratedDm :
          ActualPhysicalGeneralRigidCalibratedCenter input.certified m cfg d := calibratedD
      have d_notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified m d :=
        localizedGeneralRigidPhysicalTerminalTwinCenter_false_of_physicalCalibrated
          calibratedDm
      have physicalFix : (e : Equiv.Perm input.certified.Atom) c.1 = c.1 :=
        (centerPerm_eq_iff m e c).mp centerFixed
      have image_ne_root : m.centerPerm e d ≠ root := by
        intro h
        have valEq : (e : Equiv.Perm input.certified.Atom) a = c.1 :=
          (congrArg Subtype.val h).trans topAt
        exact (ligandBranchReaches_ne_center m c i branchMem)
          ((e : Equiv.Perm input.certified.Atom).injective
            (valEq.trans physicalFix.symm))
      have image_notTwin :
          ¬ ActualPhysicalTerminalTwinCenter input.certified m (m.centerPerm e d) := by
        intro twinImage
        exact d_notTwin
          ((actualPhysicalTerminalTwinCenter_centerPerm_iff input.certified m e d).mp
            twinImage)
      have calibratedImage :
          ActualPhysicalGeneralRigidCalibratedCenter input.certified m cfg
            (m.centerPerm e d) := by
        rcases domain.centerCase (m.centerPerm e d) image_ne_root with twinImage | calibrated
        · exact absurd twinImage image_notTwin
        · exact calibrated
      obtain ⟨frameF, alphaF, pointAtF, frameComputedF, matchF, spatialF,
        _observedF, calibrationFNonempty⟩ :=
        exists_physicalFrameAndCalibration_of_physicalGeneralRigidCenter input singleBonded
          acyclic m rfl cfg d x.occurrence xCurrent calibratedDm
      obtain ⟨frameG, alphaG, pointAtG, frameComputedG, matchG, spatialG,
        _observedG, calibrationGNonempty⟩ :=
        exists_physicalFrameAndCalibration_of_physicalGeneralRigidCenter input singleBonded
          acyclic m rfl cfg (m.centerPerm e d) y.occurrence yCurrentImage calibratedImage
      have derivedF :
          input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame x.occurrence frameF :=
        input.certified.localizedOccurrenceFourLigandFrame?_sound
          x.occurrence frameF frameComputedF
      have derivedG :
          input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame y.occurrence frameG :=
        input.certified.localizedOccurrenceFourLigandFrame?_sound
          y.occurrence frameG frameComputedG
      let centerF : input.certified.TetrahedralCenter := ⟨d.1, d.2⟩
      let centerU : input.certified.TetrahedralCenter :=
        ⟨(m.centerPerm e d).1, (m.centerPerm e d).2⟩
      have centerRealF :
          input.certified.RealTetrahedralCenterNode x.occurrence.1.node centerF :=
        ⟨carrierOccurrence_provenance_real input.certified singleBonded acyclic
            x.occurrence, by
          simpa [centerF] using xCurrent⟩
      have centerRealU :
          input.certified.RealTetrahedralCenterNode y.occurrence.1.node centerU :=
        ⟨carrierOccurrence_provenance_real input.certified singleBonded acyclic
            y.occurrence, by
          simpa [centerU] using yCurrentImage⟩
      have rigidF : ConstitutionallyRigidGraphAt input.certified.moleculeGraph centerF.1 := by
        simpa [centerF] using
          constitutionallyRigidGraphAt_of_constitutionallyRigid_detected input.certified d
            calibratedDm.1
      have rigidU : ConstitutionallyRigidGraphAt input.certified.moleculeGraph centerU.1 := by
        simpa [centerU] using
          constitutionallyRigidGraphAt_of_constitutionallyRigid_detected input.certified
            (m.centerPerm e d) calibratedImage.1
      obtain ⟨calibrationF⟩ := calibrationFNonempty
      obtain ⟨calibrationG⟩ := calibrationGNonempty
      exact
        referenceState_generalRigidAutomorphism_label_covariance input noDouble
          singleBonded acyclic hcharge m rfl cfg d e mirror c.1 physicalFix
          x.occurrence y.occurrence rootX rootY frameF frameG derivedF derivedG
          centerF centerU centerRealF centerRealU rfl rfl rigidF rigidU
          alphaF alphaG matchF matchG
          (fun index => pointAtF (alphaF index)) (fun index => pointAtG (alphaG index))
          (by simpa using spatialF) (by simpa using spatialG)
          calibrationF calibrationG (signLaw d branchMem)
  · -- Non-candidate at the source: neither endpoint is a detected center.
    have aNotMem : a ∉ input.certified.tetrahedralCenterSet := by
      intro h
      exact candidate (mem_centers_of_mem_tetrahedralCenterSet coverage h)
    have bNotMem : b ∉ input.certified.tetrahedralCenterSet := by
      intro hb
      have hImage : (graphAutOfMultiCenterAut input.certified m rfl e :
          Equiv.Perm input.certified.Atom) a ∈ input.certified.tetrahedralCenterSet := by
        simpa [graphAutOfMultiCenterAut, bEq] using hb
      exact aNotMem
        ((input.certified.moleculeGraph.mem_tetrahedralCenterSet_apply_aut_iff
          (graphAutOfMultiCenterAut input.certified m rfl e) a).mpr hImage)
    have xNone := referenceState_eq_none_of_actualPhysicalNoncandidate input noDouble
      x.occurrence ⟨a, xCurrent, aNotMem⟩
    have yNone := referenceState_eq_none_of_actualPhysicalNoncandidate input noDouble
      y.occurrence ⟨b, yCurrent, bNotMem⟩
    rw [xNone, yNone]
    cases mirror <;>
      simp [CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel]

/-- **Direct actual reader relation from the general physical domain on the fixed frame slots.**
For every pair related by `LocalizedPhysicalBranchRelation` at the actual slots, the production
dependency read at the right cursor is the uppercase reflection (when `mirror`) of the read at the
left.  On strict dependencies this is the direct reader covariance above; on non-dependencies both
reads are `none` because dependency eligibility is invariant on the branch. -/
theorem localizedGeneralRigidPhysicalBranchRelation_reader_relation_globalDomain
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (e : input.certified.detectedMultiCenterMolecule.Aut)
    (mirror : Bool) (i j : Fin 4)
    (centerFixed :
      input.certified.detectedMultiCenterMolecule.centerPerm e c = c)
    (signLaw : ∀ d : input.certified.detectedMultiCenterMolecule.Center,
      LigandBranchReaches input.certified.detectedMultiCenterMolecule c i d.1 →
      input.certified.detectedMultiCenterMolecule.configurationSign cfg d *
        permHandedness
          (input.certified.detectedMultiCenterMolecule.ligandPermAt e d) =
        (if mirror then -1 else 1) *
          input.certified.detectedMultiCenterMolecule.configurationSign cfg
            (input.certified.detectedMultiCenterMolecule.centerPerm e d))
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
        domain.graphEq c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index))) :
    ∀ x y,
      LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified
          input.certified.detectedMultiCenterMolecule domain.graphEq e) c.1
        (frame.cursorAt (alpha.symm i)) (frame.cursorAt (alpha.symm j)) x y →
      input.certified.localizedDependencyLabel
          (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
            domain.graphEq c)
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input)
            (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
              domain.graphEq c)) y =
        (if mirror then reflectUppercaseOptionalLabel else id)
          (input.certified.localizedDependencyLabel
            (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
              domain.graphEq c)
            (input.certified.localizedDependencyView
              (LocalizedUniversalReference.referenceState input)
              (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
                domain.graphEq c)) x) := by
  let m : MultiCenterMolecule input.certified.Atom :=
    input.certified.detectedMultiCenterMolecule
  let target := localizedPhysicalTopOccurrence input m domain.graphEq c
  let topCenter := localizedPhysicalTopCenter input m domain.graphEq c
  have targetRoot : target.1.root = c.1 := rfl
  have rootFixed : ((graphAutOfMultiCenterAut input.certified m domain.graphEq e :
      input.certified.moleculeGraph.Aut) : Equiv.Perm input.certified.Atom) c.1 = c.1 := by
    have physical : (e : Equiv.Perm input.certified.Atom) c.1 = c.1 :=
      (centerPerm_eq_iff m e c).mp centerFixed
    simpa [graphAutOfMultiCenterAut] using physical
  intro x y related
  by_cases depX : input.certified.LocalizedDepthDependency x.occurrence target
  · have depY : input.certified.LocalizedDepthDependency y.occurrence target :=
      (localizedPhysicalBranchRelation_dependency_iff input.certified singleBonded acyclic
        rootFixed related targetRoot).mp depX
    rw [localizedReferenceDependencyLabel_eq_state input target x depX,
      localizedReferenceDependencyLabel_eq_state input target y depY]
    exact localizedGeneralRigidPhysicalBranchRelation_referenceState_globalDomain
      input singleBonded acyclic hcharge noDouble cfg c e mirror i centerFixed signLaw
      topCenter rfl domain
      (fun x a reachable current =>
        localizedPhysicalBranchLeftMembership input singleBonded acyclic m domain.graphEq c i
          frame alpha frameComputed slotSpec reachable current)
      related depX depY
  · have depY : ¬ input.certified.LocalizedDepthDependency y.occurrence target := by
      intro dependency
      exact depX
        ((localizedPhysicalBranchRelation_dependency_iff input.certified singleBonded acyclic
          rootFixed related targetRoot).mpr dependency)
    have labelNoneX : input.certified.localizedDependencyLabel target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) x = none := by
      dsimp only [CertifiedLocalizedCIPInput.localizedDependencyLabel]
      rw [dif_neg depX]
    have labelNoneY : input.certified.localizedDependencyLabel target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) y = none := by
      dsimp only [CertifiedLocalizedCIPInput.localizedDependencyLabel]
      rw [dif_neg depY]
    rw [labelNoneX, labelNoneY]
    cases mirror <;>
      simp [CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel]

/-- **Direct proper production transport from the general physical domain.**  At the actual frame
slots the production cumulative-key observables agree at every fuel and stage. -/
theorem localizedGeneralRigidPhysicalBranchRelation_productionKey_observable_eq_proper_globalDomain
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (e : input.certified.detectedMultiCenterMolecule.Aut)
    (i j : Fin 4)
    (centerFixed :
      input.certified.detectedMultiCenterMolecule.centerPerm e c = c)
    (signLaw : ∀ d : input.certified.detectedMultiCenterMolecule.Center,
      LigandBranchReaches input.certified.detectedMultiCenterMolecule c i d.1 →
      input.certified.detectedMultiCenterMolecule.configurationSign cfg d *
        permHandedness
          (input.certified.detectedMultiCenterMolecule.ligandPermAt e d) =
        (1 : ℝ) *
          input.certified.detectedMultiCenterMolecule.configurationSign cfg
            (input.certified.detectedMultiCenterMolecule.centerPerm e d))
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
        domain.graphEq c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (stage : LocalizedCumulativeRule45Stage) :
    ∀ (fuel : Nat) (x y : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input)),
      LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified
          input.certified.detectedMultiCenterMolecule domain.graphEq e) c.1
        (frame.cursorAt (alpha.symm i)) (frame.cursorAt (alpha.symm j)) x y →
      (input.certified.buildLocalizedRerootCumulativeRule45Key? stage
          (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
            domain.graphEq c)
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input)
            (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
              domain.graphEq c)) fuel x).map
          (input.certified.localizedRerootCumulativeRule45Observable) =
        (input.certified.buildLocalizedRerootCumulativeRule45Key? stage
          (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
            domain.graphEq c)
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input)
            (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
              domain.graphEq c)) fuel y).map
          (input.certified.localizedRerootCumulativeRule45Observable) := by
  let m : MultiCenterMolecule input.certified.Atom :=
    input.certified.detectedMultiCenterMolecule
  have rootFixed : ((graphAutOfMultiCenterAut input.certified m domain.graphEq e :
      input.certified.moleculeGraph.Aut) : Equiv.Perm input.certified.Atom) c.1 = c.1 := by
    have physical : (e : Equiv.Perm input.certified.Atom) c.1 = c.1 :=
      (centerPerm_eq_iff m e c).mp centerFixed
    simpa [graphAutOfMultiCenterAut] using physical
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input :=
    globalCarrierFuel_adequate input
  let target := localizedPhysicalTopOccurrence input m domain.graphEq c
  have reader :=
    localizedGeneralRigidPhysicalBranchRelation_reader_relation_globalDomain
      input singleBonded acyclic hcharge noDouble cfg c e false i j centerFixed
      (fun d h => by simpa using signLaw d h) domain frame alpha frameComputed slotSpec
  have labels : ∀ x y,
      LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified m domain.graphEq e) c.1
        (frame.cursorAt (alpha.symm i)) (frame.cursorAt (alpha.symm j)) x y →
      input.certified.localizedDependencyLabel target
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input) target) x =
        input.certified.localizedDependencyLabel target
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input) target) y := by
    intro x y related
    have := reader x y related
    simpa using this.symm
  exact input.certified.buildLocalizedRerootCumulativeRule45Key?_map_observable_eq_of_related_sameSource
    stage target
    (input.certified.localizedDependencyView
      (LocalizedUniversalReference.referenceState input) target)
    (LocalizedPhysicalBranchRelation input.certified
      (graphAutOfMultiCenterAut input.certified m domain.graphEq e) c.1
      (frame.cursorAt (alpha.symm i)) (frame.cursorAt (alpha.symm j)))
    (fun x y related =>
      localizedPhysicalBranchRelation_atomLabel input.certified singleBonded acyclic related)
    (fun x y related =>
      localizedPhysicalBranchRelation_rootDistance input.certified singleBonded acyclic
        rootFixed related)
    (fun x y related =>
      localizedPhysicalBranchRelation_children input.certified singleBonded acyclic
        enough related)
    labels

/-- **Direct mirror production transport from the general physical domain.**  The right observable
is built at the uppercase-reflected stage. -/
theorem localizedGeneralRigidPhysicalBranchRelation_productionKey_observable_eq_mirror_globalDomain
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (e : input.certified.detectedMultiCenterMolecule.Aut)
    (i j : Fin 4)
    (centerFixed :
      input.certified.detectedMultiCenterMolecule.centerPerm e c = c)
    (signLaw : ∀ d : input.certified.detectedMultiCenterMolecule.Center,
      LigandBranchReaches input.certified.detectedMultiCenterMolecule c i d.1 →
      input.certified.detectedMultiCenterMolecule.configurationSign cfg d *
        permHandedness
          (input.certified.detectedMultiCenterMolecule.ligandPermAt e d) =
        (-1 : ℝ) *
          input.certified.detectedMultiCenterMolecule.configurationSign cfg
            (input.certified.detectedMultiCenterMolecule.centerPerm e d))
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
        domain.graphEq c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (stage : LocalizedCumulativeRule45Stage) :
    ∀ (fuel : Nat) (x y : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input)),
      LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified
          input.certified.detectedMultiCenterMolecule domain.graphEq e) c.1
        (frame.cursorAt (alpha.symm i)) (frame.cursorAt (alpha.symm j)) x y →
      (input.certified.buildLocalizedRerootCumulativeRule45Key? stage
          (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
            domain.graphEq c)
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input)
            (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
              domain.graphEq c)) fuel x).map
          (input.certified.localizedRerootCumulativeRule45Observable) =
        (input.certified.buildLocalizedRerootCumulativeRule45Key?
          (reflectLocalizedCumulativeRule45Stage stage)
          (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
            domain.graphEq c)
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input)
            (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
              domain.graphEq c)) fuel y).map
          (input.certified.localizedRerootCumulativeRule45Observable) := by
  let m : MultiCenterMolecule input.certified.Atom :=
    input.certified.detectedMultiCenterMolecule
  have rootFixed : ((graphAutOfMultiCenterAut input.certified m domain.graphEq e :
      input.certified.moleculeGraph.Aut) : Equiv.Perm input.certified.Atom) c.1 = c.1 := by
    have physical : (e : Equiv.Perm input.certified.Atom) c.1 = c.1 :=
      (centerPerm_eq_iff m e c).mp centerFixed
    simpa [graphAutOfMultiCenterAut] using physical
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input :=
    globalCarrierFuel_adequate input
  let target := localizedPhysicalTopOccurrence input m domain.graphEq c
  have reader :=
    localizedGeneralRigidPhysicalBranchRelation_reader_relation_globalDomain
      input singleBonded acyclic hcharge noDouble cfg c e true i j centerFixed
      (fun d h => by simpa using signLaw d h) domain frame alpha frameComputed slotSpec
  have readerReflect : ∀ x y,
      LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified m domain.graphEq e) c.1
        (frame.cursorAt (alpha.symm i)) (frame.cursorAt (alpha.symm j)) x y →
      input.certified.localizedDependencyLabel target
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input) target) y =
        reflectUppercaseOptionalLabel
          (input.certified.localizedDependencyLabel target
            (input.certified.localizedDependencyView
              (LocalizedUniversalReference.referenceState input) target) x) := by
    intro x y related
    have := reader x y related
    simpa using this
  have withRead :=
    input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?_map_observable_eq_of_related_reflectUppercase
      stage
      (input.certified.localizedDependencyLabel target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target))
      (input.certified.localizedDependencyLabel target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target))
      (LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified m domain.graphEq e) c.1
        (frame.cursorAt (alpha.symm i)) (frame.cursorAt (alpha.symm j)))
      (fun x y related =>
        localizedPhysicalBranchRelation_atomLabel input.certified singleBonded acyclic related)
      (fun x y related =>
        localizedPhysicalBranchRelation_rootDistance input.certified singleBonded acyclic
          rootFixed related)
      (fun x y related =>
        localizedPhysicalBranchRelation_children input.certified singleBonded acyclic
          enough related)
      readerReflect
  intro fuel x y related
  rw [← input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
        stage target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) fuel x,
    ← input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
        (reflectLocalizedCumulativeRule45Stage stage) target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) fuel y]
  exact withRead fuel x y related












theorem localizedGeneralRigidPhysicalBranch_finalOccurrence_observable_eq
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (e : input.certified.detectedMultiCenterMolecule.Aut)
    (i j : Fin 4) (mirror : Bool)
    (centerFixed :
      input.certified.detectedMultiCenterMolecule.centerPerm e c = c)
    (ligandMaps :
      input.certified.detectedMultiCenterMolecule.ligandPermAt e c i = j)
    (signLaw : ∀ d : input.certified.detectedMultiCenterMolecule.Center,
      LigandBranchReaches input.certified.detectedMultiCenterMolecule c i d.1 →
      input.certified.detectedMultiCenterMolecule.configurationSign cfg d *
        permHandedness
          (input.certified.detectedMultiCenterMolecule.ligandPermAt e d) =
        (if mirror then -1 else 1) *
          input.certified.detectedMultiCenterMolecule.configurationSign cfg
            (input.certified.detectedMultiCenterMolecule.centerPerm e d))
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c) :
    ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (alpha : Equiv.Perm (Fin 4)),
      input.certified.localizedOccurrenceFourLigandFrame?
          (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
            domain.graphEq c) = some frame ∧
        (∀ index : Fin 4,
          (frame.cursorAt index).occurrence.1.node.current? =
            some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index))) ∧
        (frame.cursorAt (alpha.symm i)).occurrence.1.node.current? =
          some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) ∧
        (frame.cursorAt (alpha.symm j)).occurrence.1.node.current? =
          some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c j) ∧
        ∀ (fuel : Nat) (stage : LocalizedCumulativeRule45Stage),
          (input.certified.buildLocalizedRerootCumulativeRule45Key? stage
              (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
                domain.graphEq c)
              (input.certified.localizedDependencyView
                (LocalizedUniversalReference.referenceState input)
                (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
                  domain.graphEq c)) fuel
              (frame.cursorAt (alpha.symm i))).map
            (input.certified.localizedRerootCumulativeRule45Observable) =
          (input.certified.buildLocalizedRerootCumulativeRule45Key?
              (if mirror then reflectLocalizedCumulativeRule45Stage stage else stage)
              (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
                domain.graphEq c)
              (input.certified.localizedDependencyView
                (LocalizedUniversalReference.referenceState input)
                (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
                  domain.graphEq c)) fuel
              (frame.cursorAt (alpha.symm j))).map
            (input.certified.localizedRerootCumulativeRule45Observable) := by
  classical
  let m : MultiCenterMolecule input.certified.Atom :=
    input.certified.detectedMultiCenterMolecule
  obtain ⟨frame, alpha, frameComputed, slotSpec, correspondence⟩ :=
    exists_localizedPhysicalTopOccurrence_frame_slotCorrespondence input singleBonded acyclic
      m domain.graphEq c e i j centerFixed ligandMaps
  let target := localizedPhysicalTopOccurrence input m domain.graphEq c
  let topCenter := localizedPhysicalTopCenter input m domain.graphEq c
  let startL := frame.cursorAt (alpha.symm i)
  let startR := frame.cursorAt (alpha.symm j)
  have targetRoot : target.1.root = c.1 := rfl
  have rootFixed : ((graphAutOfMultiCenterAut input.certified m domain.graphEq e :
      input.certified.moleculeGraph.Aut) : Equiv.Perm input.certified.Atom) c.1 = c.1 := by
    have physical : (e : Equiv.Perm input.certified.Atom) c.1 = c.1 :=
      (centerPerm_eq_iff m e c).mp centerFixed
    simpa [graphAutOfMultiCenterAut] using physical
  have relatedStart : LocalizedPhysicalBranchRelation input.certified
      (graphAutOfMultiCenterAut input.certified m domain.graphEq e) c.1
      startL startR startL startR :=
    ⟨correspondence, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  refine ⟨frame, alpha, frameComputed, slotSpec, ?_, ?_, ?_⟩
  · have h := slotSpec (alpha.symm i)
    simpa [startL] using h
  · have h := slotSpec (alpha.symm j)
    simpa [startR] using h
  · cases mirror with
    | false =>
        intro fuel stage
        exact
          localizedGeneralRigidPhysicalBranchRelation_productionKey_observable_eq_proper_globalDomain
            input singleBonded acyclic hcharge noDouble cfg c e i j centerFixed
            (fun d h => by simpa using signLaw d h) domain
            frame alpha frameComputed slotSpec stage fuel startL startR relatedStart
    | true =>
        intro fuel stage
        exact
          localizedGeneralRigidPhysicalBranchRelation_productionKey_observable_eq_mirror_globalDomain
            input singleBonded acyclic hcharge noDouble cfg c e i j centerFixed
            (fun d h => by simpa using signLaw d h) domain
            frame alpha frameComputed slotSpec stage fuel startL startR relatedStart





theorem localizedGeneralRigidPhysicalBranch_transport_observable_eq
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (i j : Fin 4) (mirror : Bool)
    (transport : BranchTransport input.certified.detectedMultiCenterMolecule cfg c i j mirror)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c) :
    ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (alpha : Equiv.Perm (Fin 4)),
      input.certified.localizedOccurrenceFourLigandFrame?
          (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
            domain.graphEq c) = some frame ∧
        (∀ index : Fin 4,
          (frame.cursorAt index).occurrence.1.node.current? =
            some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index))) ∧
        (frame.cursorAt (alpha.symm i)).occurrence.1.node.current? =
          some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) ∧
        (frame.cursorAt (alpha.symm j)).occurrence.1.node.current? =
          some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c j) ∧
        ∀ (fuel : Nat) (stage : LocalizedCumulativeRule45Stage),
          (input.certified.buildLocalizedRerootCumulativeRule45Key? stage
              (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
                domain.graphEq c)
              (input.certified.localizedDependencyView
                (LocalizedUniversalReference.referenceState input)
                (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
                  domain.graphEq c)) fuel
              (frame.cursorAt (alpha.symm i))).map
            (input.certified.localizedRerootCumulativeRule45Observable) =
          (input.certified.buildLocalizedRerootCumulativeRule45Key?
              (if mirror then reflectLocalizedCumulativeRule45Stage stage else stage)
              (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
                domain.graphEq c)
              (input.certified.localizedDependencyView
                (LocalizedUniversalReference.referenceState input)
                (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
                  domain.graphEq c)) fuel
              (frame.cursorAt (alpha.symm j))).map
            (input.certified.localizedRerootCumulativeRule45Observable) := by
  obtain ⟨e, centerFixed, ligandMaps, signLaw⟩ := transport
  exact localizedGeneralRigidPhysicalBranch_finalOccurrence_observable_eq
    input singleBonded acyclic hcharge noDouble cfg c e i j mirror centerFixed ligandMaps
    signLaw domain


















theorem localizedGeneralRigidPhysicalCompound_finalOccurrence_priorTie_and_commonReading
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (e : input.certified.detectedMultiCenterMolecule.Aut)
    (i j : Fin 4) (mirror : Bool)
    (centerFixed :
      input.certified.detectedMultiCenterMolecule.centerPerm e c = c)
    (ligandMaps :
      input.certified.detectedMultiCenterMolecule.ligandPermAt e c i = j)
    (signLaw : ∀ d : input.certified.detectedMultiCenterMolecule.Center,
      LigandBranchReaches input.certified.detectedMultiCenterMolecule c i d.1 →
      input.certified.detectedMultiCenterMolecule.configurationSign cfg d *
        permHandedness
          (input.certified.detectedMultiCenterMolecule.ligandPermAt e d) =
        (if mirror then -1 else 1) *
          input.certified.detectedMultiCenterMolecule.configurationSign cfg
            (input.certified.detectedMultiCenterMolecule.centerPerm e d))
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c) :
    ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (alpha : Equiv.Perm (Fin 4)),
      ∃ frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
          (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
            domain.graphEq c) = some frame,
        (∀ index : Fin 4,
          (frame.cursorAt index).occurrence.1.node.current? =
            some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index))) ∧
          (frame.cursorAt (alpha.symm i)).occurrence.1.node.current? =
            some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) ∧
            (frame.cursorAt (alpha.symm j)).occurrence.1.node.current? =
              some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c j) ∧
              (LocalizedPhysicalCompoundSelectorShape
                  ((localizedPhysicalCompoundFrameKeyOfComputed input
                    input.certified.detectedMultiCenterMolecule domain.graphEq c frame
                    frameComputed (alpha.symm i)).prior.references)
                  ((localizedPhysicalCompoundFrameKeyOfComputed input
                    input.certified.detectedMultiCenterMolecule domain.graphEq c frame
                    frameComputed (alpha.symm j)).prior.references)
                  mirror →
                ∃ (leftReading rightReading : input.certified.LocalizedRerootRule5Reading),
                  (localizedPhysicalCompoundFrameKeyOfComputed input
                    input.certified.detectedMultiCenterMolecule domain.graphEq c frame
                    frameComputed (alpha.symm i)).rule5Readings = [leftReading] ∧
                    (localizedPhysicalCompoundFrameKeyOfComputed input
                      input.certified.detectedMultiCenterMolecule domain.graphEq c frame
                      frameComputed (alpha.symm j)).rule5Readings = [rightReading] ∧
                      input.certified.compareLocalizedRerootCompoundRule4bcKeys
                          (localizedPhysicalCompoundFrameKeyOfComputed input
                            input.certified.detectedMultiCenterMolecule domain.graphEq c frame
                            frameComputed (alpha.symm i)).prior
                          (localizedPhysicalCompoundFrameKeyOfComputed input
                            input.certified.detectedMultiCenterMolecule domain.graphEq c frame
                            frameComputed (alpha.symm j)).prior = Ordering.eq ∧
                        LocalizedCompoundCommonReadingRelation input.certified mirror
                          leftReading rightReading) := by
  classical
  obtain ⟨frame, alpha, frameComputed, slotSpec, correspondence⟩ :=
    exists_localizedPhysicalTopOccurrence_frame_slotCorrespondence input singleBonded acyclic
      input.certified.detectedMultiCenterMolecule domain.graphEq c e i j centerFixed ligandMaps
  refine ⟨frame, alpha, frameComputed, slotSpec, ?_, ?_, ?_⟩
  · have h := slotSpec (alpha.symm i)
    simpa using h
  · have h := slotSpec (alpha.symm j)
    simpa using h
  · intro shape
    let m : MultiCenterMolecule input.certified.Atom :=
      input.certified.detectedMultiCenterMolecule
    let target := localizedPhysicalTopOccurrence input m domain.graphEq c
    let view := localizedPhysicalCompoundFrameView input m domain.graphEq c
    let derived := input.certified.localizedOccurrenceFourLigandFrame?_sound
      target frame frameComputed
    let leftKey := frame.compoundKeyAt input.certified target view derived (alpha.symm i)
    let rightKey := frame.compoundKeyAt input.certified target view derived (alpha.symm j)
    have shapeHere : LocalizedPhysicalCompoundSelectorShape
        leftKey.prior.references rightKey.prior.references mirror := by
      simpa only [leftKey, rightKey, localizedPhysicalCompoundFrameKeyOfComputed, target, view,
        derived] using shape
    have leftBuilt : input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?
        (fun cursor => input.certified.localizedDependencyLabel target view cursor)
        (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (frame.cursorAt (alpha.symm i)) = some leftKey := by
      rw [input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?_eq_localizedDependencyLabel
        target view (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (frame.cursorAt (alpha.symm i))]
      exact frame.compoundKeyAt_built input.certified target view derived (alpha.symm i)
    have rightBuilt : input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?
        (fun cursor => input.certified.localizedDependencyLabel target view cursor)
        (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (frame.cursorAt (alpha.symm j)) = some rightKey := by
      rw [input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?_eq_localizedDependencyLabel
        target view (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (frame.cursorAt (alpha.symm j))]
      exact frame.compoundKeyAt_built input.certified target view derived (alpha.symm j)
    have relatedStart : LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified m domain.graphEq e) c.1
        (frame.cursorAt (alpha.symm i)) (frame.cursorAt (alpha.symm j))
        (frame.cursorAt (alpha.symm i)) (frame.cursorAt (alpha.symm j)) :=
      ⟨correspondence, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
    have transported : ∀ stage : LocalizedCumulativeRule45Stage,
        (input.certified.buildLocalizedRerootCumulativeRule45Key? stage target view
            (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
            (frame.cursorAt (alpha.symm i))).map
          (input.certified.localizedRerootCumulativeRule45Observable) =
        (input.certified.buildLocalizedRerootCumulativeRule45Key?
            (if mirror then reflectLocalizedCumulativeRule45Stage stage else stage)
            target view (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
            (frame.cursorAt (alpha.symm j))).map
          (input.certified.localizedRerootCumulativeRule45Observable) := by
      intro stage
      cases mirror with
      | false =>
          exact localizedGeneralRigidPhysicalBranchRelation_productionKey_observable_eq_proper_globalDomain
            input singleBonded acyclic hcharge noDouble cfg c e i j centerFixed
            (fun d h => by simpa using signLaw d h) domain frame alpha frameComputed slotSpec
            stage (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
            (frame.cursorAt (alpha.symm i)) (frame.cursorAt (alpha.symm j)) relatedStart
      | true =>
          exact localizedGeneralRigidPhysicalBranchRelation_productionKey_observable_eq_mirror_globalDomain
            input singleBonded acyclic hcharge noDouble cfg c e i j centerFixed
            (fun d h => by simpa using signLaw d h) domain frame alpha frameComputed slotSpec
            stage (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
            (frame.cursorAt (alpha.symm i)) (frame.cursorAt (alpha.symm j)) relatedStart
    obtain ⟨leftPriorReading, rightPriorReading, leftReading, rightReading,
      leftPriorReadingsEq, rightPriorReadingsEq, leftRule5Eq, rightRule5Eq,
      leftReadingPriorEq, rightReadingPriorEq, priorTie, relation⟩ :=
      input.certified.localizedCompoundPriorTie_and_commonReading_of_transported
        target view mirror transported leftBuilt rightBuilt shapeHere
    refine ⟨leftReading, rightReading, ?_, ?_, ?_, relation⟩
    · simpa only [leftKey, localizedPhysicalCompoundFrameKeyOfComputed, target, view,
        derived] using leftRule5Eq
    · simpa only [rightKey, localizedPhysicalCompoundFrameKeyOfComputed, target, view,
        derived] using rightRule5Eq
    · simpa only [leftKey, rightKey, localizedPhysicalCompoundFrameKeyOfComputed, target, view,
        derived] using priorTie





theorem localizedGeneralRigidPhysicalCompound_transport_priorTie_and_commonReading
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (i j : Fin 4) (mirror : Bool)
    (transport : BranchTransport input.certified.detectedMultiCenterMolecule cfg c i j mirror)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c) :
    ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (alpha : Equiv.Perm (Fin 4)),
      ∃ frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
          (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
            domain.graphEq c) = some frame,
        (∀ index : Fin 4,
          (frame.cursorAt index).occurrence.1.node.current? =
            some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index))) ∧
          (frame.cursorAt (alpha.symm i)).occurrence.1.node.current? =
            some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) ∧
            (frame.cursorAt (alpha.symm j)).occurrence.1.node.current? =
              some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c j) ∧
              (LocalizedPhysicalCompoundSelectorShape
                  ((localizedPhysicalCompoundFrameKeyOfComputed input
                    input.certified.detectedMultiCenterMolecule domain.graphEq c frame
                    frameComputed (alpha.symm i)).prior.references)
                  ((localizedPhysicalCompoundFrameKeyOfComputed input
                    input.certified.detectedMultiCenterMolecule domain.graphEq c frame
                    frameComputed (alpha.symm j)).prior.references)
                  mirror →
                ∃ (leftReading rightReading : input.certified.LocalizedRerootRule5Reading),
                  (localizedPhysicalCompoundFrameKeyOfComputed input
                    input.certified.detectedMultiCenterMolecule domain.graphEq c frame
                    frameComputed (alpha.symm i)).rule5Readings = [leftReading] ∧
                    (localizedPhysicalCompoundFrameKeyOfComputed input
                      input.certified.detectedMultiCenterMolecule domain.graphEq c frame
                      frameComputed (alpha.symm j)).rule5Readings = [rightReading] ∧
                      input.certified.compareLocalizedRerootCompoundRule4bcKeys
                          (localizedPhysicalCompoundFrameKeyOfComputed input
                            input.certified.detectedMultiCenterMolecule domain.graphEq c frame
                            frameComputed (alpha.symm i)).prior
                          (localizedPhysicalCompoundFrameKeyOfComputed input
                            input.certified.detectedMultiCenterMolecule domain.graphEq c frame
                            frameComputed (alpha.symm j)).prior = Ordering.eq ∧
                        LocalizedCompoundCommonReadingRelation input.certified mirror
                          leftReading rightReading) := by
  obtain ⟨e, centerFixed, ligandMaps, signLaw⟩ := transport
  exact localizedGeneralRigidPhysicalCompound_finalOccurrence_priorTie_and_commonReading
    input singleBonded acyclic hcharge noDouble cfg c e i j mirror centerFixed ligandMaps
    signLaw domain

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.localizedGeneralRigidPhysicalTerminalTwinCenter_false_of_physicalCalibrated
assert_kernel_only TetraStereo.OneCenter.localizedGeneralRigidPhysicalBranchRelation_referenceState_globalDomain
assert_kernel_only TetraStereo.OneCenter.localizedGeneralRigidPhysicalBranchRelation_reader_relation_globalDomain
assert_kernel_only TetraStereo.OneCenter.localizedGeneralRigidPhysicalBranchRelation_productionKey_observable_eq_proper_globalDomain
assert_kernel_only TetraStereo.OneCenter.localizedGeneralRigidPhysicalBranchRelation_productionKey_observable_eq_mirror_globalDomain
assert_kernel_only TetraStereo.OneCenter.localizedGeneralRigidPhysicalBranch_finalOccurrence_observable_eq
assert_kernel_only TetraStereo.OneCenter.localizedGeneralRigidPhysicalBranch_transport_observable_eq
assert_kernel_only TetraStereo.OneCenter.localizedGeneralRigidPhysicalCompound_finalOccurrence_priorTie_and_commonReading
assert_kernel_only TetraStereo.OneCenter.localizedGeneralRigidPhysicalCompound_transport_priorTie_and_commonReading
