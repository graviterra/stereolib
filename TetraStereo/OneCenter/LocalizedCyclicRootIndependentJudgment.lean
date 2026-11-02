import TetraStereo.OneCenter.LocalizedCyclicRootPhysicalCorrectness
import TetraStereo.OneCenter.LocalizedRetainedCompleteMirrorCovariance
import TetraStereo.OneCenter.LocalizedFourSlotReflectionParity
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option linter.unnecessarySimpa false

/-!
# Independent cyclic root judgment with the physical pair count and letter

At the evaluator's own final root of a detected center, in the physical domain of
`CyclicRootPhysicalDomain`:

* the independent canonical predecessor-cut judgment exists (`exists_canonicalCutJudgment`):
  physical distinguishability makes the retained cut keys injective, and the physical root
  coordinates are non-coplanar;
* hence the actual current `referenceState` returns a descriptor
  (`finalRoot_referenceState_isSome`), `analyze` reports it for the center
  (`finalRoot_analyze_entry`), and the production execution returns it. Its tracked order,
  coordinate lookup and descriptor reading succeed, and the tracked pseudo count is the
  independent retained prior-pair count (`finalRoot_runtimeEvidence`);
* the returned descriptor is lowercase exactly when the physical enantiomorphic pair count of the
  detected root is one (`finalRoot_lowercase_iff_physicalCount`);
* its raw letter is the oriented-volume reading of the physical root ligand coordinates listed in
  descending order of the independent retained cut keys, which include Rule 5
  (`finalRoot_descriptor_physicalReading`). No reference is assumed to win a mirror pair;
* that raw letter is `R` exactly when the parity of the descending listing of physical ligands
  times the physical configuration sign is `-1` (`finalRoot_letter_physicalOrientation`).

The physical prior-tie converse is derived from the actual generated reader and physical
mirror transport. Every endpoint below uses only the stated physical-domain hypotheses.
-/

namespace TetraStereo.OneCenter.LocalizedCyclicRootIndependentJudgment

open CertifiedLocalizedCIPInput
open LocalizedRuleMajorReference
open DeclarativeCIP
open RootedTetrahedralBranchSymmetry
open LocalizedCyclicMatchedReadingPhysicalTransport
open LocalizedCyclicRootPhysicalSetup
open LocalizedCyclicRootPhysicalCorrectness

noncomputable section

/-- The retained keys of the canonical predecessor cuts at the final root. -/
abbrev canonicalCutKeys (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (center : input.certified.TetrahedralCenter) : Fin 4 → CompleteLigandRule5Key :=
  retainedContextualFrameKeysAt input.certified.moleculeGraph (descriptorMap input)
    (finalCenterUnit input center)
    ((finalRootFrames input singleBonded center).canonicalCutGraphs singleBonded)
    (finalRootFrames input singleBonded center).W (finalRootFrames input singleBonded center).D

variable {input : LocalizedRuleMajorReference.Input}
  {center : input.certified.TetrahedralCenter}
  {cfg : input.certified.detectedMultiCenterMolecule.Configuration}

/-! ## Existence -/

/-- **The independent canonical-cut judgment exists** at the actual final root. -/
theorem exists_canonicalCutJudgment (setup : CyclicRootPhysicalDomain input center cfg) :
    ∃ descriptor : LocalizedAuxiliaryLabel,
      RetainedContextualDescriptorJudgmentAt input.certified.moleculeGraph (descriptorMap input)
        (finalCenterUnit input center)
        ((finalRootFrames input setup.singleBonded center).canonicalCutGraphs setup.singleBonded)
        (finalRootFrames input setup.singleBonded center).W
        (finalRootFrames input setup.singleBonded center).D
        (finalRootFrames input setup.singleBonded center).actualCoordinates descriptor := by
  obtain ⟨pointAt, _observed, _nonzero, _sign, coordinates, slotNonzero⟩ :=
    frames_coordinates setup.singleBonded center setup.geometry
  obtain ⟨descriptor, judgment⟩ :=
    (LocalizedRetainedCompleteMirrorCovariance.completeRootDescriptorJudgment_exists_iff
      (canonicalCutKeys input setup.singleBonded center)
      (fun slot => pointAt
        ((finalRootFrames input setup.singleBonded center).detectedLigandPermutation slot))).2
      ⟨canonicalCutKeys_injective setup, slotNonzero⟩
  exact ⟨descriptor, fun slot => pointAt
    ((finalRootFrames input setup.singleBonded center).detectedLigandPermutation slot),
    coordinates, judgment⟩

/-- **The actual current root state is a descriptor.** -/
theorem finalRoot_referenceState_isSome (setup : CyclicRootPhysicalDomain input center cfg) :
    ∃ descriptor : LocalizedAuxiliaryLabel,
      referenceState input (finalTarget input center) = some descriptor := by
  obtain ⟨descriptor, judgment⟩ := exists_canonicalCutJudgment setup
  exact ⟨descriptor, ((finalRootFrames input setup.singleBonded center)
    |>.referenceState_some_iff_canonicalCutJudgment setup.singleBonded descriptor).2 judgment⟩

/-! ## The returned descriptor -/

/-- A returned descriptor is the independent canonical-cut judgment. -/
theorem finalRoot_canonicalCutJudgment (setup : CyclicRootPhysicalDomain input center cfg)
    {descriptor : LocalizedAuxiliaryLabel}
    (returned : referenceState input (finalTarget input center) = some descriptor) :
    RetainedContextualDescriptorJudgmentAt input.certified.moleculeGraph (descriptorMap input)
      (finalCenterUnit input center)
      ((finalRootFrames input setup.singleBonded center).canonicalCutGraphs setup.singleBonded)
      (finalRootFrames input setup.singleBonded center).W
      (finalRootFrames input setup.singleBonded center).D
      (finalRootFrames input setup.singleBonded center).actualCoordinates descriptor :=
  ((finalRootFrames input setup.singleBonded center)
    |>.referenceState_some_iff_canonicalCutJudgment setup.singleBonded descriptor).1 returned

/-- **The final report entry.** `analyze` lists the reported center with this descriptor. -/
theorem finalRoot_analyze_entry {descriptor : LocalizedAuxiliaryLabel}
    (returned : referenceState input (finalTarget input center) = some descriptor) :
    (center.val.val, some descriptor) ∈ analyze input := by
  rw [analyze_eq_referenceReport input]
  exact List.mem_map.mpr ⟨center,
    (input.certified.mem_canonicalTetrahedralCenters_iff center).mpr center.2,
    Prod.ext rfl returned⟩

/-- The production descriptor execution returns the same descriptor. -/
theorem finalRoot_exec_eq (setup : CyclicRootPhysicalDomain input center cfg)
    {descriptor : LocalizedAuxiliaryLabel}
    (returned : referenceState input (finalTarget input center) = some descriptor) :
    input.certified.ruleMajorDescriptorExec? (finalTarget input center)
        (contextOccurrenceView input (finalTarget input center)) = some descriptor :=
  ((finalRootFrames input setup.singleBonded center).exec_some_iff_retainedJudgment
    setup.singleBonded descriptor).2
    (((finalRootFrames input setup.singleBonded center).referenceState_some_iff_retainedJudgment
      setup.singleBonded descriptor).1 returned)

/-- **Runtime execution at the final root.** The production tracked order, its coordinate lookup
and its descriptor reading all succeed, and the tracked pseudo count is the independent retained
prior-pair count of the canonical cut keys. -/
theorem finalRoot_runtimeEvidence (setup : CyclicRootPhysicalDomain input center cfg)
    {descriptor : LocalizedAuxiliaryLabel}
    (returned : referenceState input (finalTarget input center) = some descriptor) :
    ∃ (tracked : TrackedLocalizedLigandOrder) (values : List CartesianPoint3) (raw : RS),
      safeTrackedOrderOrderedExecOf
          (input.certified.compareRuleMajorOccurrenceExecAt? (finalTarget input center)
            (contextOccurrenceView input (finalTarget input center))
            (finalRootFrames input setup.singleBonded center).frame) = some tracked ∧
      tracked.highestFirst.mapM (fun slot => input.certified.localizedRerootCursorSpatialPoint?
          ((finalRootFrames input setup.singleBonded center).frame.cursorAt slot)) =
        some values ∧
      descriptorOfPriorityOrderedPoints? values = some raw ∧
      descriptor = classifyTetrahedralRSPseudo raw tracked.pseudoComparisons ∧
      tracked.pseudoComparisons =
        completeRule5PairCount (canonicalCutKeys input setup.singleBonded center) := by
  have expanded := finalRoot_exec_eq setup returned
  unfold CertifiedLocalizedCIPInput.ruleMajorDescriptorExec?
    CertifiedLocalizedCIPInput.ruleMajorSpatialEvidenceExec? at expanded
  rw [(finalRootFrames input setup.singleBonded center).centerComputed,
    (finalRootFrames input setup.singleBonded center).frameComputed] at expanded
  cases trackedEq : safeTrackedOrderOrderedExecOf
      (input.certified.compareRuleMajorOccurrenceExecAt? (finalTarget input center)
        (contextOccurrenceView input (finalTarget input center))
        (finalRootFrames input setup.singleBonded center).frame) with
  | none => simp [trackedEq] at expanded
  | some tracked =>
      cases valuesEq : tracked.highestFirst.mapM (fun slot =>
          input.certified.localizedRerootCursorSpatialPoint?
            ((finalRootFrames input setup.singleBonded center).frame.cursorAt slot)) with
      | none => simp [trackedEq, valuesEq] at expanded
      | some values =>
          cases rawEq : descriptorOfPriorityOrderedPoints? values with
          | none => simp [trackedEq, valuesEq, rawEq] at expanded
          | some raw =>
              simp [trackedEq, valuesEq, rawEq] at expanded
              have count := ContextDescriptorExecutionData.trackedCount_eq_complete
                ((finalRootFrames input setup.singleBonded center).retainedExecutionData
                  setup.singleBonded)
                (retainedKeys_injective setup) tracked trackedEq
              refine ⟨tracked, values, raw, rfl, valuesEq, rawEq, expanded.symm, ?_⟩
              exact count.trans (congrArg completeRule5PairCount
                (canonicalCutKeys_eq_retainedKeys setup.singleBonded center).symm)

/-- The runtime tracked pseudo count is the physical enantiomorphic pair count. -/
theorem finalRoot_runtimePhysicalCount (setup : CyclicRootPhysicalDomain input center cfg)
    {descriptor : LocalizedAuxiliaryLabel}
    (returned : referenceState input (finalTarget input center) = some descriptor) :
    ∃ (tracked : TrackedLocalizedLigandOrder) (raw : RS),
      safeTrackedOrderOrderedExecOf
          (input.certified.compareRuleMajorOccurrenceExecAt? (finalTarget input center)
            (contextOccurrenceView input (finalTarget input center))
            (finalRootFrames input setup.singleBonded center).frame) = some tracked ∧
      descriptor = classifyTetrahedralRSPseudo raw tracked.pseudoComparisons ∧
      tracked.pseudoComparisons =
        physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule cfg center := by
  obtain ⟨tracked, _values, raw, trackedEq, _valuesEq, _rawEq, descriptorEq, count⟩ :=
    finalRoot_runtimeEvidence setup returned
  exact ⟨tracked, raw, trackedEq, descriptorEq,
    count.trans (canonicalCutPairCount_eq_physicalCount setup)⟩

/-- **Lowercase iff physical pair count one.** -/
theorem finalRoot_lowercase_iff_physicalCount (setup : CyclicRootPhysicalDomain input center cfg)
    {descriptor : LocalizedAuxiliaryLabel}
    (returned : referenceState input (finalTarget input center) = some descriptor) :
    descriptor.IsLowercase ↔
      physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule cfg center =
        1 := by
  rw [← canonicalCutPairCount_eq_physicalCount setup]
  exact (finalRootFrames input setup.singleBonded center).referenceState_lowercase_iff_canonicalCut
    setup.singleBonded returned

/-- **The letter is the physical geometric reading of the independent order.** The returned
descriptor classifies, by the physical enantiomorphic pair count, the oriented-volume letter of
the physical root ligand coordinates listed in strictly descending order of the retained cut keys. -/
theorem finalRoot_descriptor_physicalReading (setup : CyclicRootPhysicalDomain input center cfg)
    {descriptor : LocalizedAuxiliaryLabel}
    (returned : referenceState input (finalTarget input center) = some descriptor) :
    ∃ (pointAt : Fin 4 → CartesianPoint3) (order : List (Fin 4)) (raw : RS),
      (∀ i, input.certified.spatialPointAt?
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt center i) = some (pointAt i)) ∧
      order.Perm (List.finRange 4) ∧
      order.Pairwise (fun left right => canonicalCutKeys input setup.singleBonded center right <
        canonicalCutKeys input setup.singleBonded center left) ∧
      RationalTetrahedralDescriptor (order.map fun slot =>
        pointAt ((finalRootFrames input setup.singleBonded center).detectedLigandPermutation
          slot)) raw ∧
      descriptor = classifyTetrahedralRSPseudo raw
        (physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule cfg center) := by
  obtain ⟨points, order, raw, available, permutation, sorted, rational, descriptorEq⟩ :=
    (finalRootFrames input setup.singleBonded center).referenceState_eq_canonicalCut_geometric_reading
      setup.singleBonded returned
  obtain ⟨pointAt, observed, _nonzero, _sign, coordinates, _slotNonzero⟩ :=
    frames_coordinates setup.singleBonded center setup.geometry
  have pointsEq : points = fun slot => pointAt
      ((finalRootFrames input setup.singleBonded center).detectedLigandPermutation slot) := by
    funext slot
    exact Option.some.inj ((available slot).symm.trans (coordinates slot))
  subst pointsEq
  refine ⟨pointAt, order, raw, observed, permutation, sorted, rational, ?_⟩
  rw [descriptorEq, canonicalCutPairCount_eq_physicalCount setup]

/-! ## The absolute letter in physical terms -/

/-- A permutation list of the four slots lists the values of a slot permutation. -/
theorem exists_perm_eq_values {order : List (Fin 4)}
    (permutation : order.Perm (List.finRange 4)) :
    ∃ τ : Equiv.Perm (Fin 4), order = [τ 0, τ 1, τ 2, τ 3] := by
  have hlen : order.length = 4 := by simpa using permutation.length_eq
  have hnodup : order.Nodup := permutation.nodup_iff.mpr (List.nodup_finRange _)
  let f : Fin 4 → Fin 4 := fun i => order[i.1]'(by simpa [hlen] using i.isLt)
  have hinj : Function.Injective f := by
    intro i j hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnodup).mp hij)
  let τ : Equiv.Perm (Fin 4) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  refine ⟨τ, ?_⟩
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi _
    have hi4 : i < 4 := by simpa [hlen] using hi
    have hslot : order[i]'(by simpa [hlen] using hi) = τ ⟨i, hi4⟩ := by
      have : f ⟨i, hi4⟩ = order[i]'(by simpa [hlen] using hi4) := rfl
      simpa [τ, Equiv.ofBijective_apply] using this.symm
    match i with
    | 0 => simp [hslot]
    | 1 => simp [hslot]
    | 2 => simp [hslot]
    | 3 => simp [hslot]
    | n + 4 => omega

/-- **Physical orientation of a permuted listing.** If the four points have orientation `sign`,
listing them through `σ` reads `R` exactly when `permHandedness σ * sign = -1`. -/
theorem rationalDescriptor_eq_R_iff_orientation {pointAt : Fin 4 → CartesianPoint3} {sign : ℝ}
    (calibrated : rationalVolumeSign
      (CartesianPoint3.orientedVolume (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3)) = sign)
    (σ : Equiv.Perm (Fin 4)) {raw : RS}
    (rational : RationalTetrahedralDescriptor
      [pointAt (σ 0), pointAt (σ 1), pointAt (σ 2), pointAt (σ 3)] raw) :
    raw = RS.R ↔ permHandedness σ * sign = -1 := by
  have hvol := LocalizedFourSlotReflectionParity.orientedVolume_slotPermutation pointAt 1 σ
  simp only [one_mul, Equiv.Perm.one_apply] at hvol
  obtain ⟨a, b, c, d, listEq, orientation⟩ := rational
  simp only [List.cons.injEq, and_true] at listEq
  obtain ⟨rfl, rfl, rfl, rfl⟩ := listEq
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign
  · have hp : permHandedness σ = 1 := by simp [permHandedness, hsign]
    rw [hp, one_mul] at hvol
    rw [hp, one_mul]
    have same : CartesianPoint3.orientedVolume (pointAt (σ 0)) (pointAt (σ 1)) (pointAt (σ 2))
        (pointAt (σ 3)) =
        CartesianPoint3.orientedVolume (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) := by
      exact_mod_cast hvol
    cases raw with
    | R =>
        have oriented : CartesianPoint3.orientedVolume (pointAt (σ 0)) (pointAt (σ 1))
            (pointAt (σ 2)) (pointAt (σ 3)) < 0 := orientation
        rw [same] at oriented
        rw [← calibrated, rationalVolumeSign_of_neg oriented]
        norm_num
    | S =>
        have oriented : 0 < CartesianPoint3.orientedVolume (pointAt (σ 0)) (pointAt (σ 1))
            (pointAt (σ 2)) (pointAt (σ 3)) := orientation
        rw [same] at oriented
        rw [← calibrated, rationalVolumeSign_of_pos oriented]
        constructor
        · intro letter
          exact absurd letter (by decide)
        · intro product
          norm_num at product
  · have hp : permHandedness σ = -1 := by simp [permHandedness, hsign]
    rw [hp] at hvol
    rw [hp]
    have flipped : CartesianPoint3.orientedVolume (pointAt (σ 0)) (pointAt (σ 1))
        (pointAt (σ 2)) (pointAt (σ 3)) =
        -CartesianPoint3.orientedVolume (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) := by
      have cast : ((CartesianPoint3.orientedVolume (pointAt (σ 0)) (pointAt (σ 1))
          (pointAt (σ 2)) (pointAt (σ 3)) : ℚ) : ℝ) =
          ((-CartesianPoint3.orientedVolume (pointAt 0) (pointAt 1) (pointAt 2)
            (pointAt 3) : ℚ) : ℝ) := by
        rw [hvol]
        push_cast
        ring
      exact_mod_cast cast
    cases raw with
    | R =>
        have oriented : CartesianPoint3.orientedVolume (pointAt (σ 0)) (pointAt (σ 1))
            (pointAt (σ 2)) (pointAt (σ 3)) < 0 := orientation
        rw [flipped] at oriented
        have positive :
            0 < CartesianPoint3.orientedVolume (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) := by
          linarith
        rw [← calibrated, rationalVolumeSign_of_pos positive]
        norm_num
    | S =>
        have oriented : 0 < CartesianPoint3.orientedVolume (pointAt (σ 0)) (pointAt (σ 1))
            (pointAt (σ 2)) (pointAt (σ 3)) := orientation
        rw [flipped] at oriented
        have negative :
            CartesianPoint3.orientedVolume (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) < 0 := by
          linarith
        rw [← calibrated, rationalVolumeSign_of_neg negative]
        constructor
        · intro letter
          exact absurd letter (by decide)
        · intro product
          norm_num at product

/-- **The absolute letter from the physical configuration.** A returned descriptor has a slot
permutation `τ` listing the slots in strictly descending order of the independent retained cut
keys. Its raw letter is `R` exactly when the parity of the resulting listing of physical ligands,
`α * τ`, times the physical configuration sign at the root is `-1`. -/
theorem finalRoot_letter_physicalOrientation (setup : CyclicRootPhysicalDomain input center cfg)
    {descriptor : LocalizedAuxiliaryLabel}
    (returned : referenceState input (finalTarget input center) = some descriptor) :
    ∃ (τ : Equiv.Perm (Fin 4)) (raw : RS),
      [τ 0, τ 1, τ 2, τ 3].Pairwise (fun left right =>
        canonicalCutKeys input setup.singleBonded center right <
          canonicalCutKeys input setup.singleBonded center left) ∧
      (raw = RS.R ↔
        permHandedness
            ((finalRootFrames input setup.singleBonded center).detectedLigandPermutation * τ) *
          input.certified.detectedMultiCenterMolecule.configurationSign cfg center = -1) ∧
      descriptor = classifyTetrahedralRSPseudo raw
        (completeRule5PairCount (canonicalCutKeys input setup.singleBonded center)) := by
  obtain ⟨points, order, raw, available, permutation, sorted, rational, descriptorEq⟩ :=
    (finalRootFrames input setup.singleBonded center).referenceState_eq_canonicalCut_geometric_reading
      setup.singleBonded returned
  obtain ⟨pointAt, _observed, _nonzero, calibrated, coordinates, _slotNonzero⟩ :=
    frames_coordinates setup.singleBonded center setup.geometry
  have pointsEq : points = fun slot => pointAt
      ((finalRootFrames input setup.singleBonded center).detectedLigandPermutation slot) := by
    funext slot
    exact Option.some.inj ((available slot).symm.trans (coordinates slot))
  subst pointsEq
  obtain ⟨τ, orderEq⟩ := exists_perm_eq_values permutation
  subst orderEq
  exact ⟨τ, raw, sorted, rationalDescriptor_eq_R_iff_orientation calibrated
    ((finalRootFrames input setup.singleBonded center).detectedLigandPermutation * τ) rational,
    descriptorEq⟩

/-- The classified letter: the raw letter of the physical orientation, made
lowercase by the physical enantiomorphic pair count. -/
theorem finalRoot_physical_letter (setup : CyclicRootPhysicalDomain input center cfg)
    {descriptor : LocalizedAuxiliaryLabel}
    (returned : referenceState input (finalTarget input center) = some descriptor) :
    ∃ (τ : Equiv.Perm (Fin 4)) (raw : RS),
      [τ 0, τ 1, τ 2, τ 3].Pairwise (fun left right =>
        canonicalCutKeys input setup.singleBonded center right <
          canonicalCutKeys input setup.singleBonded center left) ∧
      (raw = RS.R ↔
        permHandedness
            ((finalRootFrames input setup.singleBonded center).detectedLigandPermutation * τ) *
          input.certified.detectedMultiCenterMolecule.configurationSign cfg center = -1) ∧
      descriptor = classifyTetrahedralRSPseudo raw
        (physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule cfg center) := by
  obtain ⟨τ, raw, sorted, orientation, descriptorEq⟩ :=
    finalRoot_letter_physicalOrientation setup returned
  refine ⟨τ, raw, sorted, orientation, ?_⟩
  rw [descriptorEq, canonicalCutPairCount_eq_physicalCount setup]

/-! ## Endpoint -/

/-- **General cyclic root endpoint.** In the physical domain, the actual current reference state
at the evaluator's own final root is a descriptor, it is the independent canonical-cut judgment,
it is lowercase exactly when the physical enantiomorphic pair count is one, and its letter is the
geometric reading of the physical root coordinates in the independent descending order. -/
theorem finalRoot_physical_descriptor (setup : CyclicRootPhysicalDomain input center cfg)
    :
    ∃ descriptor : LocalizedAuxiliaryLabel,
      referenceState input (finalTarget input center) = some descriptor ∧
      (center.val.val, some descriptor) ∈ analyze input ∧
      input.certified.ruleMajorDescriptorExec? (finalTarget input center)
        (contextOccurrenceView input (finalTarget input center)) = some descriptor ∧
      RetainedContextualDescriptorJudgmentAt input.certified.moleculeGraph (descriptorMap input)
        (finalCenterUnit input center)
        ((finalRootFrames input setup.singleBonded center).canonicalCutGraphs setup.singleBonded)
        (finalRootFrames input setup.singleBonded center).W
        (finalRootFrames input setup.singleBonded center).D
        (finalRootFrames input setup.singleBonded center).actualCoordinates descriptor ∧
      (descriptor.IsLowercase ↔
        physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule cfg center =
          1) ∧
      ∃ (pointAt : Fin 4 → CartesianPoint3) (order : List (Fin 4)) (raw : RS),
        (∀ i, input.certified.spatialPointAt?
          (input.certified.detectedMultiCenterMolecule.ligandAtomAt center i) =
            some (pointAt i)) ∧
        order.Perm (List.finRange 4) ∧
        order.Pairwise (fun left right => canonicalCutKeys input setup.singleBonded center right <
          canonicalCutKeys input setup.singleBonded center left) ∧
        RationalTetrahedralDescriptor (order.map fun slot =>
          pointAt ((finalRootFrames input setup.singleBonded center).detectedLigandPermutation
            slot)) raw ∧
        descriptor = classifyTetrahedralRSPseudo raw
          (physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule cfg
            center) ∧
        (raw = RS.R ↔
          ∃ τ : Equiv.Perm (Fin 4), order = [τ 0, τ 1, τ 2, τ 3] ∧
            permHandedness
                ((finalRootFrames input setup.singleBonded center).detectedLigandPermutation *
                  τ) *
              input.certified.detectedMultiCenterMolecule.configurationSign cfg center = -1) := by
  obtain ⟨descriptor, returned⟩ := finalRoot_referenceState_isSome setup
  obtain ⟨pointAt, order, raw, observed, permutation, sorted, rational, descriptorEq⟩ :=
    finalRoot_descriptor_physicalReading setup returned
  obtain ⟨_pointAt, _observed, _nonzero, calibrated, _coordinates, _slotNonzero⟩ :=
    frames_coordinates setup.singleBonded center setup.geometry
  have samePoints : _pointAt = pointAt := by
    funext i
    exact Option.some.inj ((_observed i).symm.trans (observed i))
  subst samePoints
  obtain ⟨τ, orderEq⟩ := exists_perm_eq_values permutation
  have orientation := rationalDescriptor_eq_R_iff_orientation calibrated
    ((finalRootFrames input setup.singleBonded center).detectedLigandPermutation * τ)
    (by rw [orderEq] at rational; exact rational)
  refine ⟨descriptor, returned, finalRoot_analyze_entry returned,
    finalRoot_exec_eq setup returned, finalRoot_canonicalCutJudgment setup returned,
    finalRoot_lowercase_iff_physicalCount setup returned,
    _pointAt, order, raw, observed, permutation, sorted, rational, descriptorEq, ?_⟩
  constructor
  · intro letter
    exact ⟨τ, orderEq, orientation.mp letter⟩
  · rintro ⟨τ', orderEq', product⟩
    have sameτ : τ' = τ := by
      ext k
      have values := orderEq'.symm.trans orderEq
      simp only [List.cons.injEq, and_true] at values
      obtain ⟨h0, h1, h2, h3⟩ := values
      fin_cases k
      · exact congrArg Fin.val h0
      · exact congrArg Fin.val h1
      · exact congrArg Fin.val h2
      · exact congrArg Fin.val h3
    subst sameτ
    exact orientation.mpr product

end

end TetraStereo.OneCenter.LocalizedCyclicRootIndependentJudgment

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootIndependentJudgment.canonicalCutKeys
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootIndependentJudgment.exists_canonicalCutJudgment
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootIndependentJudgment.finalRoot_referenceState_isSome
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootIndependentJudgment.finalRoot_canonicalCutJudgment
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootIndependentJudgment.finalRoot_analyze_entry
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootIndependentJudgment.finalRoot_exec_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootIndependentJudgment.finalRoot_runtimeEvidence
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootIndependentJudgment.finalRoot_runtimePhysicalCount
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootIndependentJudgment.finalRoot_lowercase_iff_physicalCount
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootIndependentJudgment.finalRoot_descriptor_physicalReading
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootIndependentJudgment.exists_perm_eq_values
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootIndependentJudgment.rationalDescriptor_eq_R_iff_orientation
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootIndependentJudgment.finalRoot_letter_physicalOrientation
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootIndependentJudgment.finalRoot_physical_letter
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootIndependentJudgment.finalRoot_physical_descriptor
