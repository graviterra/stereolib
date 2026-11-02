import TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance
import TetraStereo.OneCenter.LocalizedCyclicPhysicalTerminalTwinTransport
import TetraStereo.OneCenter.LocalizedCyclicRootBranchReaderClassification
import TetraStereo.OneCenter.LocalizedOutwardRerootDependencySupport
import TetraStereo.OneCenter.LocalizedRetainedOccurrenceTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-! # Current cyclic dependency-reader transport from physical branch transport -/

namespace TetraStereo.OneCenter
namespace LocalizedCyclicPhysicalBranchReaderTransport

open CertifiedLocalizedCIPInput
open DeclarativeCIP
open LocalizedCyclicGeneralRigidLabelCovariance
open LocalizedRuleMajorReference

noncomputable section

private theorem twinState_none
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg root)
    (target : LocalizedRuleMajorReference.Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (unitEq : input.certified.molecularFrameUnit target.1 = unit.1)
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root)
    (twin : ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule
      (cyclicContextFrameCompilation input singleBonded target real unit unitEq).center) :
    referenceState input target = none := by
  let frames := cyclicContextFrameCompilation input singleBonded target real unit unitEq
  have meaning := (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff target
    frames.center).mp frames.centerComputed
  have targetCurrent : target.1.node.current? = some frames.center.1 := meaning.2
  obtain ⟨centerAtom, leftLeaf, rightLeaf, current, _tetra, leftNeighbors, rightNeighbors,
      leavesDistinct, zEq, massEq, _chargeEq⟩ :=
    CertifiedLocalizedCIPInput.actualPhysicalTerminalTwinLeaves_of_globalTwinCenter
      input input.certified.detectedMultiCenterMolecule domain.graphEq frames.center
      target targetCurrent twin
  have centerEq : centerAtom = frames.center.1 :=
    Option.some.inj (current.symm.trans targetCurrent)
  have leftNeighbors' : input.certified.moleculeGraph.neighborFinset leftLeaf =
      {frames.center.1} := by rw [← centerEq]; exact leftNeighbors
  have rightNeighbors' : input.certified.moleculeGraph.neighborFinset rightLeaf =
      {frames.center.1} := by rw [← centerEq]; exact rightNeighbors
  exact LocalizedRuleMajorReference.referenceState_eq_none_of_actualPhysicalTerminalTwinLeaves
    input singleBonded target frames.center meaning leftLeaf rightLeaf leftNeighbors' rightNeighbors'
    leavesDistinct rootTetrahedral zEq massEq

/-- On a real detected non-twin occurrence under an actual constitutionally tied root arm, the
current generated state transports according to the physical proper/mirror action. Both source
and image strictness/calibration are derived from the cyclic physical domain. -/
theorem realDetected_state_transport_of_tiedRootArm
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (rootCursor : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (armMem : armCursor ∈ input.certified.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.certified.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armRead armRead' : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input) → Option LocalizedAuxiliaryLabel)
    {armFuel armFuel' : Nat}
    (armKey armKey' : input.certified.LocalizedRerootCumulativeRule45Key)
    (armBuilt : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead armFuel armCursor = some armKey)
    (armBuilt' : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead' armFuel' armCursor' = some armKey')
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armKey.constitutional.rule1a armKey'.constitutional.rule1a = Ordering.eq)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg root)
    (e : input.certified.moleculeGraph.Aut)
    (i j : Fin 4) (mirror : Bool)
    (transport : input.certified.DetectedBranchTransport e cfg root i j mirror)
    (target : LocalizedRuleMajorReference.Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    (inside : input.certified.RootBranchContains armCursor.occurrence target)
    (nonroot : target.1.address ≠ [])
    (rooted : root.1 = target.1.root)
    (notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule
      (cyclicContextFrameCompilation input singleBonded target real unit targetUnit).center)
    (reached : RootedTetrahedralBranchSymmetry.LigandBranchReaches
      input.certified.detectedMultiCenterMolecule root i
      ((cyclicContextFrameCompilation input singleBonded target real unit targetUnit).center).1) :
    ∃ sourceRaw imageRaw,
      referenceState input target = some (.chiral sourceRaw) ∧
      referenceState input (input.certified.transportOccurrence singleBonded e target) =
        some (.chiral imageRaw) ∧
      imageRaw = if mirror then RS.swap sourceRaw else sourceRaw := by
  let frames := cyclicContextFrameCompilation input singleBonded target real unit targetUnit
  have centerMeaning := (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff target
    frames.center).mp frames.centerComputed
  have centerNeRoot : frames.center ≠ root := by
    intro same
    have centerAtomNeRoot := LocalizedCyclicGeneralRigidPriority.current_ne_root_of_nonroot
      input.certified target real nonroot centerMeaning.2
    apply centerAtomNeRoot
    rw [← rooted]
    exact congrArg Subtype.val same
  have imageNeRoot : input.certified.physicalImageCenter e frames.center ≠ root := by
    intro same
    have eqImage : input.certified.detectedMultiCenterMolecule.centerPerm
        (input.certified.physicalDetectedAut e) frames.center = root := by
      apply Subtype.ext
      simpa [physicalImageCenter] using congrArg Subtype.val same
    apply centerNeRoot
    apply (input.certified.detectedMultiCenterMolecule.centerPerm
      (input.certified.physicalDetectedAut e)).injective
    calc
      input.certified.detectedMultiCenterMolecule.centerPerm
          (input.certified.physicalDetectedAut e) frames.center = root := eqImage
      _ = input.certified.detectedMultiCenterMolecule.centerPerm
          (input.certified.physicalDetectedAut e) root := by rw [transport.rootFixed]
  have sourceCalibrated :=
    (LocalizedCyclicGeneralRigidPriority.physicalGeneralRigid_of_domain input.certified cfg root
      domain frames.center centerNeRoot notTwin).1
  have imageNotTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule
      (input.certified.physicalImageCenter e frames.center) := by
    intro twin
    exact notTwin ((LocalizedCyclicPhysicalTerminalTwinTransport.actualPhysicalTerminalTwinCenter_transport_iff
      (input.certified.physicalDetectedAut e) frames.center).mp twin)
  have imageCalibrated :=
    (LocalizedCyclicGeneralRigidPriority.physicalGeneralRigid_of_domain input.certified cfg root
      domain (input.certified.physicalImageCenter e frames.center) imageNeRoot imageNotTwin).1
  obtain ⟨sourceRaw, sourceLabel, imageLabel⟩ :=
    LocalizedCyclicGeneralRigidLabelCovariance.referenceState_transport_of_tiedRootArm
      input singleBonded charge rootCursor rootAddress armCursor armCursor' armMem armMem'
      armDistinct armReal armReal' armRead armRead' armKey armKey' armBuilt armBuilt' tie
      target real unit targetUnit inside nonroot e cfg mirror sourceCalibrated imageCalibrated
      (by
        exact transport.signLaw (input.certified.physicalSourceCenter frames.center) reached)
  refine ⟨sourceRaw, (if mirror then RS.swap sourceRaw else sourceRaw), sourceLabel, ?_, rfl⟩
  simpa using imageLabel

/-- The twin branch of current-state transport: the physical terminal-twin predicate transports
under the same detected molecular automorphism, and the current evaluator refuses both actual
occurrences. -/
theorem terminalTwin_state_transport_none
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg root)
    (e : input.certified.moleculeGraph.Aut) (i j : Fin 4) (mirror : Bool)
    (transport : input.certified.DetectedBranchTransport e cfg root i j mirror)
    (target : LocalizedRuleMajorReference.Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (unitEq : input.certified.molecularFrameUnit target.1 = unit.1)
    (rooted : root.1 = target.1.root)
    (twin : ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule
      (cyclicContextFrameCompilation input singleBonded target real unit unitEq).center) :
    referenceState input target = none ∧
      referenceState input (input.certified.transportOccurrence singleBonded e target) = none := by
  let frames := cyclicContextFrameCompilation input singleBonded target real unit unitEq
  let imageTarget := input.certified.transportOccurrence singleBonded e target
  let imageUnit := input.certified.transportDetectedOccurrence e unit
  have rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root := by
    rw [← rooted]
    exact (input.certified.moleculeGraph.mem_tetrahedralCenterSet root.1).mp root.2
  have imageReal := transportOccurrence_real input singleBonded e target real
  have imageUnitEq := transportOccurrence_unit input singleBonded e target unit unitEq
  let imageFrames := cyclicContextFrameCompilation input singleBonded imageTarget imageReal imageUnit
    imageUnitEq
  have sourceNone := twinState_none input singleBonded cfg root domain target real unit unitEq
    rootTetrahedral twin
  have rootAtomFixed : (e : Equiv.Perm input.certified.Atom) target.1.root = target.1.root := by
    calc
      (e : Equiv.Perm input.certified.Atom) target.1.root =
          (e : Equiv.Perm input.certified.Atom) root.1 := by rw [rooted]
      _ = root.1 := by
        exact (RootedTetrahedralBranchSymmetry.centerPerm_eq_iff
          input.certified.detectedMultiCenterMolecule (input.certified.physicalDetectedAut e)
          root).mp transport.rootFixed
      _ = target.1.root := rooted
  have imageRootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter imageTarget.1.root := by
    rw [input.certified.transportOccurrence_root, rootAtomFixed]
    exact rootTetrahedral
  have imageTwinPhysical :=
    LocalizedCyclicPhysicalTerminalTwinTransport.actualPhysicalTerminalTwinCenter_transport
      (input.certified.physicalDetectedAut e) twin
  have imageCentersEq := LocalizedCyclicGeneralRigidLabelCovariance.image_center
    singleBonded e frames imageFrames
  have imageTwin : ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule imageFrames.center := by
    rw [imageCentersEq]
    exact imageTwinPhysical
  have imageNone := twinState_none input singleBonded cfg root domain imageTarget imageReal imageUnit
    imageUnitEq imageRootTetrahedral imageTwin
  exact ⟨sourceNone, imageNone⟩

/-- A real but nondetected occurrence is refused at both transported contexts. -/
theorem realNondetected_state_transport_none
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (e : input.certified.moleculeGraph.Aut)
    (target : LocalizedRuleMajorReference.Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (notDetected : ¬ IsDetectedCenter input.certified.moleculeGraph
      (input.certified.molecularFrameUnit target.1).atom) :
    referenceState input target = none ∧
      referenceState input (input.certified.transportOccurrence singleBonded e target) = none := by
  have sourceNone := LocalizedRuleMajorReference.referenceState_none_of_real_not_detected
    singleBonded target real notDetected
  have imageReal := transportOccurrence_real input singleBonded e target real
  have imageNotDetected : ¬ IsDetectedCenter input.certified.moleculeGraph
      (input.certified.molecularFrameUnit
        (input.certified.transportOccurrence singleBonded e target).1).atom := by
    rw [input.certified.molecularFrameUnit_atom_transport singleBonded e target]
    exact fun detected => notDetected
      ((input.certified.isDetectedCenter_transport_iff e
        (input.certified.molecularFrameUnit target.1).atom).mpr detected)
  exact ⟨sourceNone,
    LocalizedRuleMajorReference.referenceState_none_of_real_not_detected
      singleBonded _ imageReal imageNotDetected⟩

/-- A ring-duplicate occurrence is refused both before and after transporting its complete
root/history occurrence unit. -/
theorem ringDuplicate_state_transport_none
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (e : input.certified.moleculeGraph.Aut)
    (target : LocalizedRuleMajorReference.Occurrence input) {distance : Nat}
    (duplicate : target.1.node.provenance = OfficialCIPNodeProvenance.ringDuplicate distance) :
    referenceState input target = none ∧
      referenceState input (input.certified.transportOccurrence singleBonded e target) = none := by
  have imageDuplicate := (input.certified.transportOccurrence_provenance singleBonded e target).trans duplicate
  exact ⟨LocalizedRuleMajorReference.referenceState_none_of_ringDuplicate target duplicate,
    LocalizedRuleMajorReference.referenceState_none_of_ringDuplicate _ imageDuplicate⟩

/-- The dependency reader at a strict child is exactly the current generated fixed-point state. -/
theorem dependencyReader_eq_generatedState
    (input : LocalizedRuleMajorReference.Input)
    (target : input.certified.LocalizedCIPOccurrence (LocalizedRuleMajorReference.carrierFuel input))
    (cursor : input.certified.LocalizedRerootCursor (LocalizedRuleMajorReference.carrierFuel input))
    (dependency : input.certified.LocalizedDepthDependency cursor.occurrence target) :
    input.certified.localizedDependencyLabel target
      (input.certified.localizedDependencyView (referenceState input) target)
      cursor = referenceState input cursor.occurrence :=
  input.certified.localizedDependencyLabel_eq_state_of_dependency target
    (referenceState input) cursor dependency

/-- The actual dependency reader returns `none` at a physical terminal twin and its transported
image. The strict-dependency premise converts these current fixed-point refusals into reader
values at the two actual views. -/
theorem terminalTwin_dependencyReader_transport_none
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg root)
    (e : input.certified.moleculeGraph.Aut) (i j : Fin 4) (mirror : Bool)
    (transport : input.certified.DetectedBranchTransport e cfg root i j mirror)
    (rootCursor : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (dependency : input.certified.LocalizedDepthDependency cursor.occurrence
      rootCursor.occurrence)
    (real : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (unitEq : input.certified.molecularFrameUnit cursor.occurrence.1 = unit.1)
    (rooted : root.1 = cursor.occurrence.1.root)
    (twin : ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule
      (cyclicContextFrameCompilation input singleBonded cursor.occurrence real unit unitEq).center) :
    input.certified.localizedDependencyLabel rootCursor.occurrence
      (input.certified.localizedDependencyView (referenceState input) rootCursor.occurrence) cursor = none ∧
    input.certified.localizedDependencyLabel
      (input.certified.transportOccurrence singleBonded e rootCursor.occurrence)
      (input.certified.localizedDependencyView (referenceState input)
        (input.certified.transportOccurrence singleBonded e rootCursor.occurrence))
      (input.certified.transportCursor singleBonded e cursor) = none := by
  have imageDependency :=
    (input.certified.localizedDepthDependency_transport_iff singleBonded e cursor.occurrence
      rootCursor.occurrence).mp dependency
  have readsSource := dependencyReader_eq_generatedState input rootCursor.occurrence cursor dependency
  have readsImage := dependencyReader_eq_generatedState input
    (input.certified.transportOccurrence singleBonded e rootCursor.occurrence)
    (input.certified.transportCursor singleBonded e cursor) imageDependency
  obtain ⟨sourceNone, imageNone⟩ := terminalTwin_state_transport_none input singleBonded cfg root
    domain e i j mirror transport cursor.occurrence real unit unitEq rooted twin
  rw [readsSource, readsImage]
  exact ⟨sourceNone, imageNone⟩

/-- Nondetected real and duplicate dependency labels are `none` on both sides by the current
evaluator's own refusal gates. -/
theorem realNondetected_dependencyReader_transport_none
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (e : input.certified.moleculeGraph.Aut)
    (rootCursor cursor : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (dependency : input.certified.LocalizedDepthDependency cursor.occurrence
      rootCursor.occurrence)
    (real : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (notDetected : ¬ IsDetectedCenter input.certified.moleculeGraph
      (input.certified.molecularFrameUnit cursor.occurrence.1).atom) :
    input.certified.localizedDependencyLabel rootCursor.occurrence
      (input.certified.localizedDependencyView (referenceState input) rootCursor.occurrence) cursor = none ∧
    input.certified.localizedDependencyLabel
      (input.certified.transportOccurrence singleBonded e rootCursor.occurrence)
      (input.certified.localizedDependencyView (referenceState input)
        (input.certified.transportOccurrence singleBonded e rootCursor.occurrence))
      (input.certified.transportCursor singleBonded e cursor) = none := by
  have imageDependency :=
    (input.certified.localizedDepthDependency_transport_iff singleBonded e cursor.occurrence
      rootCursor.occurrence).mp dependency
  have readsSource := dependencyReader_eq_generatedState input rootCursor.occurrence cursor dependency
  have readsImage := dependencyReader_eq_generatedState input
    (input.certified.transportOccurrence singleBonded e rootCursor.occurrence)
    (input.certified.transportCursor singleBonded e cursor) imageDependency
  obtain ⟨sourceNone, imageNone⟩ := realNondetected_state_transport_none input singleBonded e
    cursor.occurrence real notDetected
  rw [readsSource, readsImage]
  exact ⟨sourceNone, imageNone⟩

theorem ringDuplicate_dependencyReader_transport_none
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (e : input.certified.moleculeGraph.Aut)
    (rootCursor cursor : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (dependency : input.certified.LocalizedDepthDependency cursor.occurrence
      rootCursor.occurrence) {distance : Nat}
    (duplicate : cursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.ringDuplicate distance) :
    input.certified.localizedDependencyLabel rootCursor.occurrence
      (input.certified.localizedDependencyView (referenceState input) rootCursor.occurrence) cursor = none ∧
    input.certified.localizedDependencyLabel
      (input.certified.transportOccurrence singleBonded e rootCursor.occurrence)
      (input.certified.localizedDependencyView (referenceState input)
        (input.certified.transportOccurrence singleBonded e rootCursor.occurrence))
      (input.certified.transportCursor singleBonded e cursor) = none := by
  have imageDependency :=
    (input.certified.localizedDepthDependency_transport_iff singleBonded e cursor.occurrence
      rootCursor.occurrence).mp dependency
  have readsSource := dependencyReader_eq_generatedState input rootCursor.occurrence cursor dependency
  have readsImage := dependencyReader_eq_generatedState input
    (input.certified.transportOccurrence singleBonded e rootCursor.occurrence)
    (input.certified.transportCursor singleBonded e cursor) imageDependency
  obtain ⟨sourceNone, imageNone⟩ := ringDuplicate_state_transport_none input singleBonded e
    cursor.occurrence duplicate
  rw [readsSource, readsImage]
  exact ⟨sourceNone, imageNone⟩

/-- Forward current-reader transport at an actual reached strict dependency which is a real,
detected, non-twin center. -/
theorem realDetected_dependencyReader_transport_of_tiedRootArm
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (rootCursor : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (armMem : armCursor ∈ input.certified.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.certified.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armRead armRead' : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input) → Option LocalizedAuxiliaryLabel)
    {armFuel armFuel' : Nat}
    (armKey armKey' : input.certified.LocalizedRerootCumulativeRule45Key)
    (armBuilt : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead armFuel armCursor = some armKey)
    (armBuilt' : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead' armFuel' armCursor' = some armKey')
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armKey.constitutional.rule1a armKey'.constitutional.rule1a = Ordering.eq)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg root)
    (e : input.certified.moleculeGraph.Aut)
    (i j : Fin 4) (mirror : Bool)
    (transport : input.certified.DetectedBranchTransport e cfg root i j mirror)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (inside : input.certified.RootBranchContains armCursor.occurrence cursor.occurrence)
    (nonroot : cursor.occurrence.1.address ≠ [])
    (rooted : root.1 = cursor.occurrence.1.root)
    (real : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (unitEq : input.certified.molecularFrameUnit cursor.occurrence.1 = unit.1)
    (notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule
      (cyclicContextFrameCompilation input singleBonded cursor.occurrence real unit unitEq).center)
    (reached : RootedTetrahedralBranchSymmetry.LigandBranchReaches
      input.certified.detectedMultiCenterMolecule root i
      ((cyclicContextFrameCompilation input singleBonded cursor.occurrence real unit unitEq).center).1)
    (dependency : input.certified.LocalizedDepthDependency cursor.occurrence
      rootCursor.occurrence) :
    ∃ sourceRaw imageRaw,
      input.certified.localizedDependencyLabel rootCursor.occurrence
        (input.certified.localizedDependencyView (referenceState input) rootCursor.occurrence)
        cursor = some (.chiral sourceRaw) ∧
      input.certified.localizedDependencyLabel
        (input.certified.transportOccurrence singleBonded e rootCursor.occurrence)
        (input.certified.localizedDependencyView (referenceState input)
          (input.certified.transportOccurrence singleBonded e rootCursor.occurrence))
        (input.certified.transportCursor singleBonded e cursor) = some (.chiral imageRaw) ∧
      imageRaw = if mirror then RS.swap sourceRaw else sourceRaw := by
  have imageDependency :=
    (input.certified.localizedDepthDependency_transport_iff singleBonded e cursor.occurrence
      rootCursor.occurrence).mp dependency
  have sourceRead := dependencyReader_eq_generatedState input rootCursor.occurrence cursor dependency
  have imageRead := dependencyReader_eq_generatedState input
    (input.certified.transportOccurrence singleBonded e rootCursor.occurrence)
    (input.certified.transportCursor singleBonded e cursor) imageDependency
  obtain ⟨sourceRaw, imageRaw, sourceState, imageState, related⟩ :=
    realDetected_state_transport_of_tiedRootArm input singleBonded charge rootCursor rootAddress
      armCursor armCursor' armMem armMem' armDistinct armReal armReal' armRead armRead' armKey
      armKey' armBuilt armBuilt' tie cfg root domain e i j mirror transport cursor.occurrence
      real unit unitEq inside nonroot rooted notTwin reached
  refine ⟨sourceRaw, imageRaw, ?_, ?_, related⟩
  · simpa [sourceRead] using sourceState
  · simpa [imageRead] using imageState

end
end LocalizedCyclicPhysicalBranchReaderTransport
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalBranchReaderTransport.realDetected_state_transport_of_tiedRootArm
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalBranchReaderTransport.terminalTwin_state_transport_none
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalBranchReaderTransport.realNondetected_state_transport_none
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalBranchReaderTransport.ringDuplicate_state_transport_none
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalBranchReaderTransport.dependencyReader_eq_generatedState
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalBranchReaderTransport.terminalTwin_dependencyReader_transport_none
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalBranchReaderTransport.realNondetected_dependencyReader_transport_none
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalBranchReaderTransport.ringDuplicate_dependencyReader_transport_none
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalBranchReaderTransport.realDetected_dependencyReader_transport_of_tiedRootArm
