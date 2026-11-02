import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalInverse
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# What the retained R/S profile observes: blind transport and bridgehead parity

The actual evaluator reads auxiliary centers only through their generated R/S/r/s labels. A
refused auxiliary center contributes `none`, whatever its configuration. This module states that
observation limit without the reader.

* `BlindSignLaw`: an automorphism obeys the physical sign law at every real center reached from a
  root slot, **except** at reached occurrences where both the occurrence and its image carry a
  reader-free refusal witness (`HistoryRefusalWitness`).
* `law_of_reach_blind`: under a blind sign law the actual generated states are transported by
  `retainedPhysicalLetter` at every reached occurrence (well-founded induction on the actual
  dependency order; refused occurrences are handled by their witnesses, all others by the
  calibrated step `law_of_calibrated`).
* `retainedKeys_eq_of_blindProper`, `referenceState_none_of_blindProper`,
  `priorTie_of_blindMirror`: consequences at the root.
* `blindSignLaw_of_detectedTransport`: every physical branch transport is blind, so these
  statements contain the accepted forward results.
* `pairParity_transport`: the bridgehead parity `s(d₁)·s(d₃)` is preserved by every proper *and*
  every mirror transport whose handedness is coupled at `d₁, d₃`; it is the achiral quantity that a
  blind transport may change.

No sign law is assumed at witnessed occurrences; no reader agreement, order, label or output is
assumed anywhere.
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityEvidence

open CertifiedLocalizedCIPInput LocalizedRuleMajorReference DeclarativeCIP
open DeclarativeCIP.RetainedOccurrenceCarrier DeclarativeCIP.RetainedCutArm
open DeclarativeCIP.RetainedCutAutomorphism
open LocalizedCumulativeDecoratedTree Rule4aTableBridge OfficialSparseCanonicalVectorComparison
open LocalizedRetainedMirrorDescriptorCorrectness LocalizedRecursiveAuxiliaryPhysicalDomain
open LocalizedCyclicGeneralRigidLabelCovariance LocalizedCyclicGeneralRigidPriority
open LocalizedCyclicMatchedReadingPhysicalTransport LocalizedCyclicRootArmReachability
open LocalizedCyclicPhysicalStageTransport LocalizedCyclicPhysicalMirrorPriorTie
open LocalizedRecursiveAuxiliaryPhysicalTransport LocalizedRecursiveAuxiliaryPhysicalCorrectness
open LocalizedRecursiveAuxiliaryPhysicalInverse
open RootedTetrahedralBranchSymmetry
open scoped Classical

noncomputable section

/-! ## The bridgehead parity invariant -/

section Parity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Transport law of the bridgehead parity.** If an automorphism obeys the sign law, with either
mirror flag, at two centers where it acts with equal handedness, it preserves the product of their
configuration signs. Proper and mirror transports both preserve it: it is achiral. -/
theorem pairParity_transport (m : MultiCenterMolecule V) (cfg : m.Configuration) (e : m.Aut)
    (mirror : Bool) (d₁ d₃ : m.Center)
    (law₁ : m.configurationSign cfg d₁ * permHandedness (m.ligandPermAt e d₁) =
      (if mirror then -1 else 1) * m.configurationSign cfg (m.centerPerm e d₁))
    (law₃ : m.configurationSign cfg d₃ * permHandedness (m.ligandPermAt e d₃) =
      (if mirror then -1 else 1) * m.configurationSign cfg (m.centerPerm e d₃))
    (coupled : permHandedness (m.ligandPermAt e d₁) = permHandedness (m.ligandPermAt e d₃)) :
    m.configurationSign cfg (m.centerPerm e d₁) * m.configurationSign cfg (m.centerPerm e d₃) =
      m.configurationSign cfg d₁ * m.configurationSign cfg d₃ := by
  rw [← coupled] at law₃
  have hand := permHandedness_mul_self (m.ligandPermAt e d₁)
  have factor : ((if mirror then -1 else 1 : ℝ)) * (if mirror then -1 else 1) = 1 := by
    cases mirror <;> norm_num
  calc m.configurationSign cfg (m.centerPerm e d₁) * m.configurationSign cfg (m.centerPerm e d₃)
      = ((if mirror then -1 else 1 : ℝ) * (if mirror then -1 else 1)) *
          (m.configurationSign cfg (m.centerPerm e d₁) *
            m.configurationSign cfg (m.centerPerm e d₃)) := by rw [factor, one_mul]
    _ = ((if mirror then -1 else 1) * m.configurationSign cfg (m.centerPerm e d₁)) *
          ((if mirror then -1 else 1) * m.configurationSign cfg (m.centerPerm e d₃)) := by ring
    _ = (m.configurationSign cfg d₁ * permHandedness (m.ligandPermAt e d₁)) *
          (m.configurationSign cfg d₃ * permHandedness (m.ligandPermAt e d₁)) := by
        rw [law₁, law₃]
    _ = m.configurationSign cfg d₁ * m.configurationSign cfg d₃ := by
        rw [show (m.configurationSign cfg d₁ * permHandedness (m.ligandPermAt e d₁)) *
            (m.configurationSign cfg d₃ * permHandedness (m.ligandPermAt e d₁)) =
            m.configurationSign cfg d₁ * m.configurationSign cfg d₃ *
              (permHandedness (m.ligandPermAt e d₁) * permHandedness (m.ligandPermAt e d₁)) by
            ring, hand, mul_one]

end Parity

/-! ## Blind transport -/

section Blind

variable {input : Input} {rootTarget : Occurrence input}
  {rootUnit : DetectedOccurrence input.certified.moleculeGraph}
  {rootTargetUnit : input.certified.molecularFrameUnit rootTarget.1 = rootUnit.1}

/-- **Blind sign law.** At every real reached center the physical sign law holds, unless both the
occurrence and its transported image carry a reader-free refusal witness. -/
def BlindSignLaw (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (i : Fin 4) (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (e : input.certified.moleculeGraph.Aut)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration) (mirror : Bool) : Prop :=
  ∀ z : Occurrence input, Reach rootFrames i z →
    z.1.node.provenance = OfficialCIPNodeProvenance.realAtom →
    ∀ d : input.certified.detectedMultiCenterMolecule.Center, z.1.node.current? = some d.1 →
      (input.certified.detectedMultiCenterMolecule.configurationSign cfg d *
          permHandedness (input.certified.detectedMultiCenterMolecule.ligandPermAt
            (input.certified.physicalDetectedAut e) d) =
        physicalMirrorFactor mirror *
          input.certified.detectedMultiCenterMolecule.configurationSign cfg
            (input.certified.detectedMultiCenterMolecule.centerPerm
              (input.certified.physicalDetectedAut e) d)) ∨
      ((∀ a, z.1.node.current? = some a → HistoryRefusalWitness input cfg z.1.node.history a) ∧
        (∀ a, (input.certified.transportOccurrence singleBonded e z).1.node.current? = some a →
          HistoryRefusalWitness input cfg
            (input.certified.transportOccurrence singleBonded e z).1.node.history a))

/-- Every physical branch transport is blind: its sign law holds at every reached center. -/
theorem blindSignLaw_of_detectedTransport
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = .realAtom)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (e : input.certified.moleculeGraph.Aut) {i j : Fin 4} (mirror : Bool)
    (transport : input.certified.DetectedBranchTransport e cfg rootFrames.center
      (rootFrames.detectedLigandPermutation i) (rootFrames.detectedLigandPermutation j) mirror) :
    BlindSignLaw rootFrames i singleBonded e cfg mirror := by
  rintro z ⟨cursor, cursorEq, reachable⟩ real d current
  left
  subst cursorEq
  exact transport.signLaw d (reach_ligandBranchReaches singleBonded rootFrames rootAddress rootReal
    i cursor reachable real d.1 current)

/-- One step of the blind induction. -/
theorem blind_step
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = .realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg rootFrames.center)
    (e : input.certified.moleculeGraph.Aut) (mirror : Bool)
    (rootArmFixed : (e : Equiv.Perm input.certified.Atom) rootFrames.center.1 = rootFrames.center.1)
    (ligandSent : (e : Equiv.Perm input.certified.Atom)
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
          (rootFrames.detectedLigandPermutation i)) =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
        (rootFrames.detectedLigandPermutation j))
    (blind : BlindSignLaw rootFrames i singleBonded e cfg mirror)
    (target : Occurrence input) (reach : Reach rootFrames i target)
    (ih : ∀ z, input.certified.LocalizedDepthDependency z target → Reach rootFrames i z →
      Law singleBonded e mirror z) :
    Law singleBonded e mirror target := by
  have tie := rootArms_rule1aTie_of_atoms singleBonded rootFrames rootAddress rootReal e
    rootArmFixed ligandSent
  have rootFixed : input.certified.detectedMultiCenterMolecule.centerPerm
      (input.certified.physicalDetectedAut e) rootFrames.center = rootFrames.center :=
    (RootedTetrahedralBranchSymmetry.centerPerm_eq_iff
      input.certified.detectedMultiCenterMolecule (input.certified.physicalDetectedAut e)
      rootFrames.center).mpr rootArmFixed
  have sentSlot := rootSlot_sent singleBonded rootFrames rootAddress rootReal e rootArmFixed
    ligandSent
  have reachTarget := reach
  obtain ⟨cursor, cursorEq, reachable⟩ := reach
  obtain ⟨⟨previous, previousEq, shorter⟩, inside, nonroot, rooted⟩ :=
    cursor_facts rootFrames rootAddress rootReal i cursor reachable
  rw [cursorEq] at shorter inside nonroot rooted
  by_cases real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom
  swap
  · have source := referenceState_none_of_not_real input target real
    have image := referenceState_none_of_not_real input
      (input.certified.transportOccurrence singleBonded e target) (by
        rw [input.certified.transportOccurrence_provenance singleBonded e target]
        exact real)
    unfold Law
    rw [source, image]
    rfl
  by_cases detected : IsDetectedCenter input.certified.moleculeGraph
      (input.certified.molecularFrameUnit target.1).atom
  swap
  · obtain ⟨source, image⟩ :=
      LocalizedCyclicPhysicalBranchReaderTransport.realNondetected_state_transport_none input
        singleBonded e target real detected
    unfold Law
    rw [source, image]
    rfl
  let unit : DetectedOccurrence input.certified.moleculeGraph :=
    ⟨input.certified.molecularFrameUnit target.1, detected⟩
  let frames := cyclicContextFrameCompilation input singleBonded target real unit rfl
  have centerMeaning := (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff target
    frames.center).mp frames.centerComputed
  have imageUnitEq := transportOccurrence_unit input singleBonded e target unit rfl
  have imageReal := transportOccurrence_real input singleBonded e target real
  rcases blind target reachTarget real (input.certified.physicalSourceCenter frames.center)
      centerMeaning.2 with signAtCenter | ⟨sourceWitness, imageWitness⟩
  swap
  · -- Both the occurrence and its image are refused, by reader-free witnesses.
    have sourceNone := referenceState_none_of_historyWitness singleBonded rootFrames rootAddress
      rootReal distinct e rootArmFixed ligandSent cfg domain target reachTarget real detected
      sourceWitness
    have invFixed : ((e⁻¹ : input.certified.moleculeGraph.Aut) : Equiv.Perm input.certified.Atom)
        rootFrames.center.1 = rootFrames.center.1 := by
      show (e : Equiv.Perm input.certified.Atom)⁻¹ rootFrames.center.1 = rootFrames.center.1
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact rootArmFixed.symm
    have invSent : ((e⁻¹ : input.certified.moleculeGraph.Aut) : Equiv.Perm input.certified.Atom)
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
          (rootFrames.detectedLigandPermutation j)) =
        input.certified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
          (rootFrames.detectedLigandPermutation i) := by
      show (e : Equiv.Perm input.certified.Atom)⁻¹ _ = _
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact ligandSent.symm
    have imageDetected : IsDetectedCenter input.certified.moleculeGraph
        (input.certified.molecularFrameUnit
          (input.certified.transportOccurrence singleBonded e target).1).atom := by
      rw [imageUnitEq]
      exact (input.certified.transportDetectedOccurrence e unit).2
    have imageNone := referenceState_none_of_historyWitness singleBonded rootFrames rootAddress
      rootReal (Ne.symm distinct) e⁻¹ invFixed invSent cfg domain
      (input.certified.transportOccurrence singleBonded e target)
      (reach_transport singleBonded rootFrames e sentSlot reachTarget) imageReal imageDetected
      imageWitness
    unfold Law
    rw [sourceNone, imageNone]
    rfl
  -- Otherwise the sign law holds at the target center: the calibrated step.
  have dNe : input.certified.physicalSourceCenter frames.center ≠ rootFrames.center := by
    intro same
    have atomNe := current_ne_root_of_nonroot input.certified target real nonroot centerMeaning.2
    apply atomNe
    rw [← rooted]
    exact congrArg Subtype.val same
  have imageNe : input.certified.physicalImageCenter e frames.center ≠ rootFrames.center := by
    intro same
    apply dNe
    apply (input.certified.detectedMultiCenterMolecule.centerPerm
      (input.certified.physicalDetectedAut e)).injective
    calc input.certified.detectedMultiCenterMolecule.centerPerm
          (input.certified.physicalDetectedAut e) (input.certified.physicalSourceCenter frames.center)
        = input.certified.physicalImageCenter e frames.center := rfl
      _ = rootFrames.center := same
      _ = input.certified.detectedMultiCenterMolecule.centerPerm
          (input.certified.physicalDetectedAut e) rootFrames.center := rootFixed.symm
  let imageFrames := cyclicContextFrameCompilation input singleBonded
    (input.certified.transportOccurrence singleBonded e target) imageReal
    (input.certified.transportDetectedOccurrence e unit) imageUnitEq
  by_cases twin : ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule frames.center
  · have rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root := by
      rw [← rooted]
      exact (input.certified.moleculeGraph.mem_tetrahedralCenterSet rootFrames.center.1).mp
        rootFrames.center.2
    have sourceNone := twinState_none input singleBonded target real unit rfl rootTetrahedral twin
    have imageTwin : ActualPhysicalTerminalTwinCenter input.certified
        input.certified.detectedMultiCenterMolecule imageFrames.center := by
      rw [image_center singleBonded e frames imageFrames]
      exact LocalizedCyclicPhysicalTerminalTwinTransport.actualPhysicalTerminalTwinCenter_transport
        (input.certified.physicalDetectedAut e) twin
    have imageRootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter
        (input.certified.transportOccurrence singleBonded e target).1.root := by
      rw [input.certified.transportOccurrence_root, ← rooted, rootArmFixed, rooted]
      exact rootTetrahedral
    have imageNone := twinState_none input singleBonded
      (input.certified.transportOccurrence singleBonded e target) imageReal
      (input.certified.transportDetectedOccurrence e unit) imageUnitEq imageRootTetrahedral imageTwin
    unfold Law
    rw [sourceNone, imageNone]
    rfl
  have imageNotTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule
      (input.certified.physicalImageCenter e frames.center) := fun imageTwin =>
    twin ((LocalizedCyclicPhysicalTerminalTwinTransport.actualPhysicalTerminalTwinCenter_transport_iff
      (input.certified.physicalDetectedAut e) (input.certified.physicalSourceCenter frames.center)).mp
      imageTwin)
  obtain ⟨sourcePointAt, sourceObserved, _sourceNonzero, sourceSign⟩ :=
    (domain.centerCase _ dNe).resolve_left twin
  obtain ⟨imagePointAt, imageObserved, _imageNonzero, imageSign⟩ :=
    (domain.centerCase _ imageNe).resolve_left imageNotTwin
  let framesW : ContextFrameCompilation input target unit rfl :=
    { frames with
      W := max frames.W imageFrames.W
      D := max frames.D imageFrames.D
      widthBound := fun k => (frames.widthBound k).trans (le_max_left _ _)
      depthBound := fun k => (frames.depthBound k).trans (le_max_left _ _) }
  let imageFramesW : ContextFrameCompilation input
      (input.certified.transportOccurrence singleBonded e target)
      (input.certified.transportDetectedOccurrence e unit) imageUnitEq :=
    { imageFrames with
      W := max frames.W imageFrames.W
      D := max frames.D imageFrames.D
      widthBound := fun k => (imageFrames.widthBound k).trans (le_max_right _ _)
      depthBound := fun k => (imageFrames.depthBound k).trans (le_max_right _ _) }
  have realI := (rootFrame_cursor_facts singleBonded rootFrames rootAddress rootReal i).1
  have realJ := (rootFrame_cursor_facts singleBonded rootFrames rootAddress rootReal j).1
  have armDistinct : (rootFrames.frame.cursorAt i).occurrence ≠
      (rootFrames.frame.cursorAt j).occurrence := by
    intro same
    have currents := congrArg
      (fun occurrence : Occurrence input => occurrence.1.node.current?) same
    simp only at currents
    rw [rootFrames.ligandAt i, rootFrames.ligandAt j] at currents
    exact distinct (rootFrames.detectedLigandPermutation.injective
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt_injective rootFrames.center
        (Option.some.inj currents)))
  have oldI := (input.certified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized
    (contextOccurrenceRead input rootTarget) _ _).symm.trans (rootFrames.stages i).a.built
  have oldJ := (input.certified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized
    (contextOccurrenceRead input rootTarget) _ _).symm.trans (rootFrames.stages j).a.built
  obtain ⟨parent, _parentClass, others⟩ :=
    parentSlot_separated_of_rootArmRule1aTie input.certified singleBonded
      { occurrence := rootTarget, previous? := none } rootAddress
      (rootFrames.frame.cursorAt i) (rootFrames.frame.cursorAt j) (rootFrames.childAt i)
      (rootFrames.childAt j) armDistinct realI realJ (contextOccurrenceRead input rootTarget)
      (contextOccurrenceRead input rootTarget) (rootFrames.stages i).a.key
      (rootFrames.stages j).a.key oldI oldJ tie target real inside framesW.frame
      (LocalizedCyclicGeneralRigidGeneratedLabels.frame_computed framesW) nonroot
  have outwardReads : ∀ slot, slot ≠ parent →
      ReadsAgree input.certified.moleculeGraph e (descriptorMap input)
        (mirroredMap input.certified.moleculeGraph mirror (descriptorMap input)) unit
        (framesW.canonicalCutGraphs singleBonded slot) := by
    intro slot ne
    have outSlot := (others slot ne).1
    have deeperSlot : target.1.address.length <
        (framesW.frame.cursorAt slot).occurrence.1.address.length := by
      obtain ⟨k, addressEq⟩ := outSlot
      rw [addressEq]
      simp
    have step : CertifiedLocalizedCIPInput.E input.certified cursor
        (framesW.frame.cursorAt slot) :=
      frame_outward_mem_children singleBonded framesW cursor cursorEq previous previousEq
        shorter outSlot
    have armReads : ReadsAgree input.certified.moleculeGraph e (descriptorMap input)
        (mirroredMap input.certified.moleculeGraph mirror (descriptorMap input)) unit
        (framesW.actualArmGraphs slot) := by
      intro node steps occ _nodeReal ancestors context
      obtain ⟨source, sourceReach, sourceUnit⟩ :=
        actualArm_read_source singleBonded framesW slot node steps occ ancestors context
      have dependency := (input.certified.outward_reachable_dependency target
        (framesW.frame.cursorAt slot) source (framesW.childAt slot) deeperSlot sourceReach).1
      have sourceRoot : Reach rootFrames i source.occurrence :=
        ⟨source, rfl, (reachable.tail step).trans sourceReach⟩
      exact covariant_of_law singleBonded e mirror source.occurrence occ sourceUnit
        (ih source.occurrence dependency sourceRoot)
    let iso : RootedDigraph.Iso (framesW.canonicalCutGraphs singleBonded slot)
        (framesW.actualArmGraphs slot) :=
      Classical.choice (framesW.canonicalLigandCut singleBonded slot).faithful
    exact readsAgree_of_iso e (descriptorMap input)
      (mirroredMap input.certified.moleculeGraph mirror (descriptorMap input)) unit iso.symm armReads
  have sourceAvailable : ∀ slot, framesW.actualCoordinates slot =
      some (sourcePointAt (framesW.detectedLigandPermutation slot)) := fun slot =>
    sourceObserved _
  have imageCenterEq := image_center singleBonded e framesW imageFramesW
  have imageAvailable : ∀ slot, imageFramesW.actualCoordinates slot =
      some (imagePointAt (imageFramesW.detectedLigandPermutation slot)) := by
    intro slot
    show input.certified.spatialPointAt?
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt imageFramesW.center
        (imageFramesW.detectedLigandPermutation slot)) = _
    rw [imageCenterEq]
    exact imageObserved _
  have imageSign' : rationalVolumeSign (slotVolume imagePointAt) =
      input.certified.detectedMultiCenterMolecule.configurationSign cfg imageFramesW.center := by
    rw [imageCenterEq]
    exact imageSign
  have sign := slotVolume_sign_of_calibrated singleBonded e framesW imageFramesW cfg mirror
    signAtCenter sourcePointAt imagePointAt sourceSign imageSign'
  exact law_of_calibrated singleBonded e mirror framesW imageFramesW rfl rfl parent
    (fun slot ne => (others slot ne).2) outwardReads _ _ sourceAvailable imageAvailable sign

/-- **The actual evaluator is invariant under blind transport.** Every occurrence reached from the
transported root slot satisfies the transport law, with refused auxiliary centers exempt from the
sign law. -/
theorem law_of_reach_blind
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = .realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg rootFrames.center)
    (e : input.certified.moleculeGraph.Aut) (mirror : Bool)
    (rootArmFixed : (e : Equiv.Perm input.certified.Atom) rootFrames.center.1 = rootFrames.center.1)
    (ligandSent : (e : Equiv.Perm input.certified.Atom)
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
          (rootFrames.detectedLigandPermutation i)) =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
        (rootFrames.detectedLigandPermutation j))
    (blind : BlindSignLaw rootFrames i singleBonded e cfg mirror)
    (target : Occurrence input) (reach : Reach rootFrames i target) :
    Law singleBonded e mirror target := by
  have main : ∀ z, Reach rootFrames i z → Law singleBonded e mirror z := by
    intro z
    refine @WellFounded.induction _ _
      (input.certified.localizedDepthDependency_wellFounded (carrierFuel input))
      (fun z => Reach rootFrames i z → Law singleBonded e mirror z) z ?_
    intro z ih reachZ
    exact blind_step singleBonded rootFrames rootAddress rootReal distinct cfg domain e mirror
      rootArmFixed ligandSent blind z reachZ (fun w dependency reachW => ih w dependency reachW)
  exact main target reach

/-- Covariant reads of the transported root arm under a blind transport. -/
theorem canonicalCut_readsAgree_blind
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = .realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg rootFrames.center)
    (e : input.certified.moleculeGraph.Aut) (mirror : Bool)
    (rootArmFixed : (e : Equiv.Perm input.certified.Atom) rootFrames.center.1 = rootFrames.center.1)
    (ligandSent : (e : Equiv.Perm input.certified.Atom)
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
          (rootFrames.detectedLigandPermutation i)) =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
        (rootFrames.detectedLigandPermutation j))
    (blind : BlindSignLaw rootFrames i singleBonded e cfg mirror) :
    ReadsAgree input.certified.moleculeGraph e (descriptorMap input)
      (mirroredMap input.certified.moleculeGraph mirror (descriptorMap input)) rootUnit
      (rootFrames.canonicalCutGraphs singleBonded i) := by
  have armReads : ReadsAgree input.certified.moleculeGraph e (descriptorMap input)
      (mirroredMap input.certified.moleculeGraph mirror (descriptorMap input)) rootUnit
      (rootFrames.actualArmGraphs i) := by
    intro node steps occ _real ancestors context
    obtain ⟨source, sourceReach, sourceUnit⟩ :=
      actualArm_read_source singleBonded rootFrames i node steps occ ancestors context
    exact covariant_of_law singleBonded e mirror source.occurrence occ sourceUnit
      (law_of_reach_blind singleBonded rootFrames rootAddress rootReal distinct cfg domain e mirror
        rootArmFixed ligandSent blind source.occurrence ⟨source, rfl, sourceReach⟩)
  let iso : RootedDigraph.Iso (rootFrames.canonicalCutGraphs singleBonded i)
      (rootFrames.actualArmGraphs i) :=
    Classical.choice (rootFrames.canonicalLigandCut singleBonded i).faithful
  exact readsAgree_of_iso e (descriptorMap input)
    (mirroredMap input.certified.moleculeGraph mirror (descriptorMap input)) rootUnit iso.symm
    armReads

/-- **Blind proper transport gives equal complete root keys.** -/
theorem retainedKeys_eq_of_blindProper
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = .realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg rootFrames.center)
    (e : input.certified.moleculeGraph.Aut)
    (rootArmFixed : (e : Equiv.Perm input.certified.Atom) rootFrames.center.1 = rootFrames.center.1)
    (ligandSent : (e : Equiv.Perm input.certified.Atom)
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
          (rootFrames.detectedLigandPermutation i)) =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
        (rootFrames.detectedLigandPermutation j))
    (blind : BlindSignLaw rootFrames i singleBonded e cfg false) :
    rootFrames.retainedKeys i = rootFrames.retainedKeys j :=
  retainedKeys_eq_of_readsAgree singleBonded rootFrames e
    (transportOccurrence_fixed_of_history singleBonded e rootTarget
      (rootHistory_fixed rootFrames rootAddress rootReal e rootArmFixed))
    (rootSlot_sent singleBonded rootFrames rootAddress rootReal e rootArmFixed ligandSent)
    (canonicalCut_readsAgree_blind singleBonded rootFrames rootAddress rootReal distinct cfg domain
      e false rootArmFixed ligandSent blind)

/-- **Blind proper transport makes the root refuse.** -/
theorem referenceState_none_of_blindProper
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = .realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg rootFrames.center)
    (e : input.certified.moleculeGraph.Aut)
    (rootArmFixed : (e : Equiv.Perm input.certified.Atom) rootFrames.center.1 = rootFrames.center.1)
    (ligandSent : (e : Equiv.Perm input.certified.Atom)
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
          (rootFrames.detectedLigandPermutation i)) =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
        (rootFrames.detectedLigandPermutation j))
    (blind : BlindSignLaw rootFrames i singleBonded e cfg false) :
    referenceState input rootTarget = none := by
  have equal := retainedKeys_eq_of_blindProper singleBonded rootFrames rootAddress rootReal
    distinct cfg domain e rootArmFixed ligandSent blind
  rw [rootFrames.referenceState_none_iff_no_retainedJudgment singleBonded]
  rintro ⟨descriptor, points, _available, judgment⟩
  exact distinct (completeRootDescriptorJudgment_injective judgment equal)

/-- **Blind mirror transport gives an actual prior tie.** -/
theorem priorTie_of_blindMirror
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = .realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg rootFrames.center)
    (e : input.certified.moleculeGraph.Aut)
    (rootArmFixed : (e : Equiv.Perm input.certified.Atom) rootFrames.center.1 = rootFrames.center.1)
    (ligandSent : (e : Equiv.Perm input.certified.Atom)
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
          (rootFrames.detectedLigandPermutation i)) =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
        (rootFrames.detectedLigandPermutation j))
    (blind : BlindSignLaw rootFrames i singleBonded e cfg true) :
    input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (rootFrames.compounds i).prior (rootFrames.compounds j).prior = .eq :=
  priorTie_of_readsAgree_and_cursor_transport singleBonded rootFrames e
    (transportOccurrence_fixed_of_history singleBonded e rootTarget
      (rootHistory_fixed rootFrames rootAddress rootReal e rootArmFixed))
    (rootSlot_sent singleBonded rootFrames rootAddress rootReal e rootArmFixed ligandSent)
    (canonicalCut_readsAgree_blind singleBonded rootFrames rootAddress rootReal distinct cfg domain
      e true rootArmFixed ligandSent blind)

end Blind

end

end TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityEvidence

assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityEvidence.pairParity_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityEvidence.BlindSignLaw
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityEvidence.blindSignLaw_of_detectedTransport
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityEvidence.blind_step
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityEvidence.law_of_reach_blind
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityEvidence.canonicalCut_readsAgree_blind
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityEvidence.retainedKeys_eq_of_blindProper
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityEvidence.referenceState_none_of_blindProper
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityEvidence.priorTie_of_blindMirror
