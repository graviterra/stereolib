import TetraStereo.OneCenter.LocalizedRecursiveGlobalRootCovariance
import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryIndependentSemantics
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-!
# Root-changing physical covariance at every retained occurrence

The recursive state at an occurrence is determined by four retained root cuts. Every actual
context read in those cuts has a strictly longer molecular path. Induction on remaining carrier
path length therefore supplies all four reader agreements at once, including the parent cut.
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveAllOccurrenceCovariance

noncomputable section

open TetraStereo.OneCenter
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport
open TetraStereo.OneCenter.LocalizedRecursiveGlobalRootCovariance
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryIndependentSemantics
open TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance
open TetraStereo.OneCenter.LocalizedCyclicPhysicalStageTransport
open TetraStereo.OneCenter.LocalizedRetainedMirrorDescriptorCorrectness
open TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
open TetraStereo.OneCenter.AcyclicCutBranchAutomorphism
open CertifiedLocalizedCIPInput LocalizedRuleMajorReference DeclarativeCIP
open DeclarativeCIP.RetainedOccurrenceCarrier DeclarativeCIP.RetainedCutArm
open DeclarativeCIP.RetainedCutAutomorphism
open scoped Classical

variable {input : LocalizedRuleMajorReference.Input}

private theorem actualReferenceOccurrence_mapDetected_some
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (e : input.certified.moleculeGraph.Aut)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (occurrence : Occurrence input)
    (chosen : actualReferenceOccurrenceOf input unit.1 = some occurrence) :
    actualReferenceOccurrenceOf input (mapDetected input.certified.moleculeGraph e unit).1 =
      some (input.certified.transportOccurrence singleBonded e occurrence) := by
  have unitEq := (actualReferenceOccurrenceOf_eq_some_iff_of_simpleBonded input singleBonded
    unit.1 occurrence).mp chosen
  apply (actualReferenceOccurrenceOf_eq_some_iff_of_simpleBonded input singleBonded
    (mapDetected input.certified.moleculeGraph e unit).1
    (input.certified.transportOccurrence singleBonded e occurrence)).2
  rw [input.certified.molecularFrameUnit_transport singleBonded e occurrence, unitEq]
  rfl

private theorem actualReferenceOccurrence_mapDetected_none
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (e : input.certified.moleculeGraph.Aut)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (chosen : actualReferenceOccurrenceOf input unit.1 = none) :
    actualReferenceOccurrenceOf input (mapDetected input.certified.moleculeGraph e unit).1 = none := by
  cases imageChosen : actualReferenceOccurrenceOf input
      (mapDetected input.certified.moleculeGraph e unit).1 with
  | none => rfl
  | some imageOccurrence =>
      have imageUnitEq := (actualReferenceOccurrenceOf_eq_some_iff_of_simpleBonded input
        singleBonded (mapDetected input.certified.moleculeGraph e unit).1 imageOccurrence).mp
        imageChosen
      let sourceOccurrence := input.certified.transportOccurrence singleBonded e⁻¹ imageOccurrence
      have sourceUnitEq : input.certified.molecularFrameUnit sourceOccurrence.1 = unit.1 := by
        rw [input.certified.molecularFrameUnit_transport singleBonded e⁻¹ imageOccurrence,
          imageUnitEq]
        change transportOccurrenceUnit (e : Equiv.Perm input.certified.Atom).symm
          (transportOccurrenceUnit (e : Equiv.Perm input.certified.Atom) unit.1) = unit.1
        exact transportOccurrenceUnit_symm_apply (e : Equiv.Perm input.certified.Atom) unit.1
      have sourceChosen := (actualReferenceOccurrenceOf_eq_some_iff_of_simpleBonded input
        singleBonded unit.1 sourceOccurrence).2 sourceUnitEq
      rw [chosen] at sourceChosen
      cases sourceChosen

private theorem readsAgree_of_deeperLaws
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (e : input.certified.moleculeGraph.Aut) (mirror : Bool)
    (target : Occurrence input) (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    (targetReal : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (deeperLaw : ∀ source : Occurrence input,
      target.1.node.provenance = OfficialCIPNodeProvenance.realAtom →
      source.1.node.provenance = OfficialCIPNodeProvenance.realAtom →
      (input.certified.molecularFrameUnit target.1).path.length <
        (input.certified.molecularFrameUnit source.1).path.length →
      Law singleBonded e mirror source)
    (graph : RootedDigraph input.certified.Atom) :
    ReadsAgree input.certified.moleculeGraph e (descriptorMap input)
      (mirroredMap input.certified.moleculeGraph mirror (descriptorMap input)) unit graph := by
  intro node steps occ _real hsteps read
  cases chosen : actualReferenceOccurrenceOf input occ.1 with
  | none =>
      have imageChosen := actualReferenceOccurrence_mapDetected_none singleBonded e occ chosen
      have imageMap : descriptorMap input (mapDetected input.certified.moleculeGraph e occ) = none := by
        simp [descriptorMap, imageChosen]
      have rawSourceMap : descriptorMap input occ = none := by
        simp [descriptorMap, chosen]
      have sourceMap : mirroredMap input.certified.moleculeGraph mirror
          (descriptorMap input) occ = none := by
        cases mirror <;> simp [mirroredMap, DescriptorMap.reflect, rawSourceMap]
      rw [imageMap, sourceMap]
  | some source =>
      have sourceUnitEq := (actualReferenceOccurrenceOf_eq_some_iff_of_simpleBonded input
        singleBonded occ.1 source).mp chosen
      have deeper : (input.certified.molecularFrameUnit target.1).path.length <
          (input.certified.molecularFrameUnit source.1).path.length := by
        rw [targetUnit, sourceUnitEq]
        exact contextOccurrence_path_lt read
      have sourceLaw : Law singleBonded e mirror source := by
        by_cases sourceReal : source.1.node.provenance = OfficialCIPNodeProvenance.realAtom
        · exact deeperLaw source targetReal sourceReal deeper
        · have sourceNone := referenceState_none_of_not_real input source sourceReal
          have imageNone := referenceState_none_of_not_real input
            (input.certified.transportOccurrence singleBonded e source) (by
              rw [input.certified.transportOccurrence_provenance singleBonded e source]
              exact sourceReal)
          unfold Law
          rw [sourceNone, imageNone]
          rfl
      exact covariant_of_law singleBonded e mirror source occ sourceUnitEq sourceLaw

/-- The generated auxiliary state transports under a global physical sign law. Calibrated
coordinates are required at every detected center; no root is fixed and no branch-specific
parent separation is assumed. -/
theorem referenceState_transport_allOccurrences
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (calibrated : ∀ center : input.certified.detectedMultiCenterMolecule.Center,
      ActualPhysicalCalibratedCoordinates input.certified
        input.certified.detectedMultiCenterMolecule cfg center)
    (e : input.certified.moleculeGraph.Aut) (mirror : Bool)
    (signLaw : ∀ center : input.certified.detectedMultiCenterMolecule.Center,
      input.certified.detectedMultiCenterMolecule.configurationSign cfg center *
        permHandedness (input.certified.detectedMultiCenterMolecule.ligandPermAt
          (input.certified.physicalDetectedAut e) center) =
        physicalMirrorFactor mirror *
          input.certified.detectedMultiCenterMolecule.configurationSign cfg
            (input.certified.detectedMultiCenterMolecule.centerPerm
              (input.certified.physicalDetectedAut e) center))
    (target : Occurrence input) :
    Law singleBonded e mirror target := by
  have main : ∀ n, ∀ target : Occurrence input,
      target.1.node.provenance = OfficialCIPNodeProvenance.realAtom →
      Fintype.card input.certified.Atom -
          (input.certified.molecularFrameUnit target.1).path.length = n →
      Law singleBonded e mirror target := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro target real measure
      by_cases detected : IsDetectedCenter input.certified.moleculeGraph
          (input.certified.molecularFrameUnit target.1).atom
      swap
      · obtain ⟨source, image⟩ :=
          LocalizedCyclicPhysicalBranchReaderTransport.realNondetected_state_transport_none
            input singleBonded e target real detected
        unfold Law
        rw [source, image]
        rfl
      let unit : DetectedOccurrence input.certified.moleculeGraph :=
        ⟨input.certified.molecularFrameUnit target.1, detected⟩
      let frames := cyclicContextFrameCompilation input singleBonded target real unit rfl
      have imageUnitEq := transportOccurrence_unit input singleBonded e target unit rfl
      have imageReal := transportOccurrence_real input singleBonded e target real
      let imageFrames := cyclicContextFrameCompilation input singleBonded
        (input.certified.transportOccurrence singleBonded e target) imageReal
        (input.certified.transportDetectedOccurrence e unit) imageUnitEq
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
      have reads : ∀ slot, ReadsAgree input.certified.moleculeGraph e (descriptorMap input)
          (mirroredMap input.certified.moleculeGraph mirror (descriptorMap input)) unit
          (framesW.canonicalCutGraphs singleBonded slot) := by
        intro slot
        exact readsAgree_of_deeperLaws singleBonded e mirror target unit rfl real
          (fun source _ sourceReal deeper => ih
            (Fintype.card input.certified.Atom -
              (input.certified.molecularFrameUnit source.1).path.length)
            (by
            have bound := realUnitPath_length_le source sourceReal
            have targetBound := realUnitPath_length_le target real
            omega)
            source sourceReal rfl)
          (framesW.canonicalCutGraphs singleBonded slot)
      obtain ⟨sourcePointAt, sourceObserved, _sourceNonzero, sourceSign⟩ := calibrated framesW.center
      obtain ⟨imagePointAt, imageObserved, _imageNonzero, imageSign⟩ := calibrated imageFramesW.center
      let sourcePoints : Fin 4 → CartesianPoint3 :=
        fun slot => sourcePointAt (framesW.detectedLigandPermutation slot)
      let imagePoints : Fin 4 → CartesianPoint3 :=
        fun slot => imagePointAt (imageFramesW.detectedLigandPermutation slot)
      have sourceAvailable : ∀ slot, framesW.actualCoordinates slot = some (sourcePoints slot) := by
        intro slot
        exact sourceObserved _
      have imageAvailable : ∀ slot, imageFramesW.actualCoordinates slot = some (imagePoints slot) := by
        intro slot
        show input.certified.spatialPointAt?
          (input.certified.detectedMultiCenterMolecule.ligandAtomAt imageFramesW.center
            (imageFramesW.detectedLigandPermutation slot)) = _
        exact imageObserved _
      have sign := slotVolume_sign_of_calibrated singleBonded e framesW imageFramesW cfg mirror
        (signLaw (input.certified.physicalSourceCenter framesW.center))
        sourcePointAt imagePointAt sourceSign imageSign
      have sameW : imageFramesW.W = framesW.W := rfl
      have sameD : imageFramesW.D = framesW.D := rfl
      exact referenceState_transport_of_rootCutReads singleBonded framesW e mirror imageFramesW
        sameW sameD reads sourcePoints imagePoints sourceAvailable imageAvailable sign
  by_cases real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom
  · exact main _ target real rfl
  · have source := referenceState_none_of_not_real input target real
    have image := referenceState_none_of_not_real input
      (input.certified.transportOccurrence singleBonded e target) (by
        rw [input.certified.transportOccurrence_provenance singleBonded e target]
        exact real)
    unfold Law
    rw [source, image]
    rfl

end
end TetraStereo.OneCenter.LocalizedRecursiveAllOccurrenceCovariance

assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveAllOccurrenceCovariance.referenceState_transport_allOccurrences
