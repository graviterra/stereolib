import TetraStereo.OneCenter.LocalizedPhysicalInputReflection
import TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySourceModel
import TetraStereo.OneCenter.LocalizedRetainedMirrorDescriptorCorrectness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Source-to-reflected-input covariance of the actual reference pipeline

`reflectInput input` (`LocalizedPhysicalInputReflection`) is a **different certified input**: its
spatial table is the `x ↦ -x` mirror of the original's, and every other field is unchanged. This
module compares the actual generated state and report of the two inputs. It is not the
same-input automorphism transport of `LocalizedRecursiveAllOccurrenceCovariance`; no graph
automorphism, physical configuration or sign law at other centers is assumed.

Proof route (no supplied reader, label, frame or priority correspondence):

1. `outcomeAt_reflect`: one retained outcome judgment on four cut graphs, read through a
   descriptor map `dm` at coordinates `p`, gives the judgment through `dm.reflect` at the reflected
   coordinates with letter `reflectUppercaseAuxiliaryLabel` (= `retainedPhysicalLetter true`).
   Refusal (`none`) is preserved via the involution. This is
   `completeRootDescriptorJudgment_retainedPhysical true graphs 1` with the sign equation from
   `orientedVolume_reflectX`.
2. `stateMap_mirroredState`: the descriptor map read by the reflected input from the mirrored
   candidate state is the reflection of the original actual descriptor map. Units are unchanged
   and the occurrence lookup is transported through the unique occurrence of each unit.
3. `mirroredState_sourceRetainedModel`: the mirrored candidate
   `z' ↦ (referenceState input (unmapOcc z')).map reflectUppercaseAuxiliaryLabel` satisfies the
   accepted **source-only** retained model of the reflected input. Source frames, source cut
   graphs and source coordinates of the reflected input are those of the original
   (`noDoubleFrame_reflected`, `sourceCutGraphs_reflected`), with coordinates reflected
   (`sourceCoordinates_reflected`).
4. `referenceState_reflectInput`: by `sourceRetainedModel_unique`, the actual generated state of
   the reflected input is the mirrored candidate, at **every** occurrence: refused, non-real,
   non-center, lowercase and uppercase states included.
5. `mem_analyze_reflectInput_iff`: the whole actual report of the reflected input is the original
   report with every successful label mapped by `reflectUppercaseAuxiliaryLabel`; refusals stay
   refusals.

The hypothesis is only `SimpleBonded` (finite single-bond input), as for the source model.
Nothing is said about whether the produced labels are chemically correct; this module proves
that the actual evaluator commutes with the established descriptor reflection across inputs.
-/

namespace TetraStereo.OneCenter.LocalizedReferenceInputMirrorCovariance

open CertifiedLocalizedCIPInput LocalizedRuleMajorReference DeclarativeCIP
open LocalizedRecursiveAuxiliaryIndependentSemantics LocalizedRecursiveAuxiliarySourceWindows
open LocalizedRetainedSourceCutFrames LocalizedRecursiveAuxiliarySourceModel
open LocalizedRetainedMirrorDescriptorCorrectness LocalizedPhysicalInputReflection
open scoped Classical

noncomputable section

/-! ## Label algebra -/

theorem reflectUppercase_involutive (label : LocalizedAuxiliaryLabel) :
    reflectUppercaseAuxiliaryLabel (reflectUppercaseAuxiliaryLabel label) = label :=
  retainedPhysicalLetter_involutive true label

theorem localizedAuxiliaryDescriptor_reflectUppercase (label : LocalizedAuxiliaryLabel) :
    localizedAuxiliaryDescriptor (reflectUppercaseAuxiliaryLabel label) =
      (localizedAuxiliaryDescriptor label).reflect := by
  rcases label with raw | raw <;> cases raw <;> rfl

theorem descriptorMap_reflect_reflect {Unit : Type*} (dm : DescriptorMap Unit) :
    dm.reflect.reflect = dm := by
  funext unit
  unfold DescriptorMap.reflect
  cases dm unit with
  | none => rfl
  | some d => cases d <;> rfl

theorem option_map_reflectUppercase_eq_iff (left right : Option LocalizedAuxiliaryLabel) :
    left.map reflectUppercaseAuxiliaryLabel = right ↔
      left = right.map reflectUppercaseAuxiliaryLabel := by
  constructor
  · rintro rfl
    cases left <;> simp [reflectUppercase_involutive]
  · rintro rfl
    cases right <;> simp [reflectUppercase_involutive]

/-! ## One retained outcome under coordinate reflection -/

section Outcome

universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (unit : DetectedOccurrence molecule)
  (graphs : Fin 4 → RootedDigraph Atom) (W D : Nat)

theorem judgmentAt_reflect (dm : DescriptorMap (DetectedOccurrence molecule))
    (coordinates : Fin 4 → Option CartesianPoint3) (descriptor : LocalizedAuxiliaryLabel)
    (judgment : RetainedContextualDescriptorJudgmentAt molecule dm unit graphs W D coordinates
      descriptor) :
    RetainedContextualDescriptorJudgmentAt molecule dm.reflect unit graphs W D
      (fun slot => (coordinates slot).map CartesianPoint3.reflectX)
      (reflectUppercaseAuxiliaryLabel descriptor) := by
  obtain ⟨points, observed, complete⟩ := judgment
  refine ⟨fun slot => CartesianPoint3.reflectX (points slot), fun slot => ?_, ?_⟩
  · show (coordinates slot).map CartesianPoint3.reflectX = _
    rw [observed slot]
    rfl
  · have hsign : rationalVolumeSign
        (slotVolume (fun slot => CartesianPoint3.reflectX (points slot))) =
        physicalMirrorFactor true * permHandedness 1 * rationalVolumeSign (slotVolume points) := by
      unfold slotVolume
      rw [CartesianPoint3.orientedVolume_reflectX, rationalVolumeSign_neg]
      simp [physicalMirrorFactor]
    have image := completeRootDescriptorJudgment_retainedPhysical molecule dm unit true graphs 1
      points (fun slot => CartesianPoint3.reflectX (points slot)) W D descriptor hsign complete
    have keyEq : retainedImageKey molecule dm unit true graphs 1 W D =
        retainedContextualFrameKeysAt molecule dm.reflect unit graphs W D := by
      funext slot
      simp [retainedImageKey, retainedContextualFrameKeysAt]
    rw [keyEq] at image
    exact image

/-- **One retained outcome under reflection.** Success maps by `reflectUppercaseAuxiliaryLabel`;
refusal stays refusal. -/
theorem outcomeAt_reflect (dm : DescriptorMap (DetectedOccurrence molecule))
    (coordinates : Fin 4 → Option CartesianPoint3) (outcome : Option LocalizedAuxiliaryLabel)
    (holds : RetainedContextualOutcomeAt molecule dm unit graphs W D coordinates outcome) :
    RetainedContextualOutcomeAt molecule dm.reflect unit graphs W D
      (fun slot => (coordinates slot).map CartesianPoint3.reflectX)
      (outcome.map reflectUppercaseAuxiliaryLabel) := by
  cases outcome with
  | some descriptor => exact judgmentAt_reflect molecule unit graphs W D dm coordinates descriptor holds
  | none =>
      rintro ⟨descriptor, image⟩
      apply holds
      refine ⟨reflectUppercaseAuxiliaryLabel descriptor, ?_⟩
      have back := judgmentAt_reflect molecule unit graphs W D dm.reflect _ descriptor image
      rw [descriptorMap_reflect_reflect] at back
      have coordinatesEq : (fun slot => ((coordinates slot).map CartesianPoint3.reflectX).map
          CartesianPoint3.reflectX) = coordinates := by
        funext slot
        cases coordinates slot <;> simp [CartesianPoint3.reflectX_involutive]
      rw [coordinatesEq] at back
      exact back

end Outcome

/-! ## The mirrored candidate state of the reflected input -/

variable {input : Input}

/-- The original actual state read through the inverse occurrence map and the established
descriptor reflection. A candidate only: its equality with the reflected input's actual state is
proved below. -/
def mirroredState (input : Input) :
    Occurrence (reflectInput input) → Option LocalizedAuxiliaryLabel :=
  fun occurrence => (referenceState input (unmapOcc occurrence)).map reflectUppercaseAuxiliaryLabel

theorem mirroredState_mapOcc (occurrence : Occurrence input) :
    mirroredState input (mapOcc occurrence) =
      (referenceState input occurrence).map reflectUppercaseAuxiliaryLabel := rfl

/-- Occurrence lookup is transported: the reflected input's occurrence of a unit is the image of
the original's. -/
theorem actualReferenceOccurrenceOf_reflectInput
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (unit : OccurrenceUnit input.certified.Atom) :
    actualReferenceOccurrenceOf (reflectInput input) unit =
      (actualReferenceOccurrenceOf input unit).map mapOcc := by
  cases original : actualReferenceOccurrenceOf input unit with
  | some occurrence =>
      have unitEq := (actualReferenceOccurrenceOf_eq_some_iff_of_simpleBonded input singleBonded
        unit occurrence).mp original
      exact (actualReferenceOccurrenceOf_eq_some_iff_of_simpleBonded (reflectInput input)
        singleBonded unit (mapOcc occurrence)).mpr unitEq
  | none =>
      cases reflected : actualReferenceOccurrenceOf (reflectInput input) unit with
      | none => rfl
      | some occurrence =>
          exfalso
          have unitEq := (actualReferenceOccurrenceOf_eq_some_iff_of_simpleBonded
            (reflectInput input) singleBonded unit occurrence).mp reflected
          have back := (actualReferenceOccurrenceOf_eq_some_iff_of_simpleBonded input
            singleBonded unit (unmapOcc occurrence)).mpr unitEq
          rw [original] at back
          cases back

/-- **Reflected descriptor map.** The reflected input reads, from the mirrored candidate, the
reflection of the original actual descriptor map. -/
theorem stateMap_mirroredState (singleBonded : input.certified.moleculeGraph.SimpleBonded) :
    stateMap (reflectInput input) (mirroredState input) =
      (stateMap input (referenceState input)).reflect := by
  funext unit
  unfold stateMap DescriptorMap.reflect
  rw [actualReferenceOccurrenceOf_reflectInput singleBonded unit.1]
  beta_reduce
  cases actualReferenceOccurrenceOf input unit.1 with
  | none => rfl
  | some occurrence =>
      simp only [Option.map_some, Option.bind_some, mirroredState_mapOcc, Option.map_map]
      apply congrArg (fun f => Option.map f (referenceState input occurrence))
      funext label
      exact localizedAuxiliaryDescriptor_reflectUppercase label

/-! ## Source frame data of the reflected input -/

theorem sourceFrame_reflectInput (target : Occurrence input) :
    sourceFrame? (input := reflectInput input) (mapOcc target) =
      (sourceFrame? target).map mapFrame4 :=
  noDoubleFrame_reflected input.certified target

theorem sourceCutGraphs_reflected (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : Occurrence input)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input)) :
    sourceCutGraphs (input := reflectInput input) singleBonded (mapOcc target) (mapFrame4 frame) =
      sourceCutGraphs singleBonded target frame := by
  funext slot
  unfold sourceCutGraphs
  rw [cursorAt_reflected]
  rfl

theorem sourceCoordinates_reflected
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input)) :
    sourceCoordinates (input := reflectInput input) (mapFrame4 frame) =
      fun slot => (sourceCoordinates frame slot).map CartesianPoint3.reflectX := by
  funext slot
  unfold sourceCoordinates
  rw [cursorAt_reflected]
  exact cursorSpatialPoint_reflected input.certified _

/-! ## The source model of the reflected input -/

/-- **The mirrored candidate is a source retained model of the reflected input.** Derived from the
original actual state's source model; no equality with the reflected input's actual state is
assumed. -/
theorem mirroredState_sourceRetainedModel
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) :
    SourceRetainedModel (reflectInput input) singleBonded (mirroredState input) := by
  intro target
  obtain ⟨original, rfl⟩ : ∃ original : Occurrence input, target = mapOcc original :=
    ⟨unmapOcc target, rfl⟩
  have model := referenceState_sourceRetainedModel singleBonded original
  refine ⟨fun notReal => ?_, fun real notDetected => ?_, ?_⟩
  · rw [mirroredState_mapOcc, model.1 notReal]
    rfl
  · rw [mirroredState_mapOcc, model.2.1 real notDetected]
    rfl
  · intro real detected frame' computed'
    rw [sourceFrame_reflectInput] at computed'
    cases computedEq : sourceFrame? original with
    | none =>
        rw [computedEq] at computed'
        cases computed'
    | some frame =>
        rw [computedEq] at computed'
        cases computed'
        have holds := model.2.2 real detected frame computedEq
        dsimp only at holds ⊢
        rw [sourceCutGraphs_reflected, sourceCoordinates_reflected,
          stateMap_mirroredState singleBonded, mirroredState_mapOcc]
        exact outcomeAt_reflect _ _ _ _ _ _ _ _ holds

/-! ## Actual-state covariance at every occurrence -/

/-- **The actual generated state of the reflected input is the mirrored candidate.** -/
theorem referenceState_reflectInput (singleBonded : input.certified.moleculeGraph.SimpleBonded) :
    referenceState (reflectInput input) = mirroredState input :=
  (sourceRetainedModel_unique (input := reflectInput input) singleBonded
    (mirroredState_sourceRetainedModel singleBonded)).symm

/-- **All-occurrence cross-input covariance.** At every occurrence of a finite single-bond input,
including refused, non-real, non-center and lowercase states, the reflected input's actual state
is the original actual state under `retainedPhysicalLetter true`. -/
theorem referenceState_reflectInput_mapOcc
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) (occurrence : Occurrence input) :
    referenceState (reflectInput input) (mapOcc occurrence) =
      (referenceState input occurrence).map (retainedPhysicalLetter true) := by
  rw [referenceState_reflectInput singleBonded]
  rfl

theorem referenceState_reflectInput_none_iff
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) (occurrence : Occurrence input) :
    referenceState (reflectInput input) (mapOcc occurrence) = none ↔
      referenceState input occurrence = none := by
  rw [referenceState_reflectInput_mapOcc singleBonded]
  simp

/-- The actual descriptor map of the reflected input is the reflected actual descriptor map. -/
theorem descriptorMap_reflectInput (singleBonded : input.certified.moleculeGraph.SimpleBonded) :
    descriptorMap (reflectInput input) = (descriptorMap input).reflect := by
  rw [← stateMap_referenceState, ← stateMap_referenceState, referenceState_reflectInput singleBonded]
  exact stateMap_mirroredState singleBonded

/-! ## Whole-report covariance -/

theorem finalOccurrence_reflectInput (center : input.certified.TetrahedralCenter) :
    (reflectInput input).certified.localizedFinalOccurrenceExecutable
        (carrierFuel (reflectInput input)) center =
      mapOcc (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center) :=
  rfl

/-- **Actual report covariance.** Every report entry of the reflected input is an entry of the
original report with its outcome mapped by the established descriptor reflection, and
conversely. Refusals stay refusals; uppercase swaps; lowercase is fixed. -/
theorem mem_analyze_reflectInput_iff (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (atom : Nat) (outcome : Option LocalizedAuxiliaryLabel) :
    (atom, outcome) ∈ analyze (reflectInput input) ↔
      (atom, outcome.map reflectUppercaseAuxiliaryLabel) ∈ analyze input := by
  rw [mem_analyze_iff_sourceRetainedModel (input := reflectInput input) singleBonded
      (mirroredState_sourceRetainedModel singleBonded),
    mem_analyze_iff_sourceRetainedModel singleBonded (referenceState_sourceRetainedModel singleBonded)]
  constructor
  · rintro ⟨center, centerEq, stateEq⟩
    refine ⟨center, centerEq, ?_⟩
    rw [finalOccurrence_reflectInput, mirroredState_mapOcc] at stateEq
    exact (option_map_reflectUppercase_eq_iff _ _).mp stateEq
  · rintro ⟨center, centerEq, stateEq⟩
    refine ⟨center, centerEq, ?_⟩
    rw [finalOccurrence_reflectInput, mirroredState_mapOcc]
    exact (option_map_reflectUppercase_eq_iff _ _).mpr stateEq

theorem mem_analyze_reflectInput_map_iff
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (atom : Nat) (outcome : Option LocalizedAuxiliaryLabel) :
    (atom, outcome.map (retainedPhysicalLetter true)) ∈ analyze (reflectInput input) ↔
      (atom, outcome) ∈ analyze input := by
  rw [mem_analyze_reflectInput_iff singleBonded]
  have back : (outcome.map (retainedPhysicalLetter true)).map reflectUppercaseAuxiliaryLabel =
      outcome := by
    cases outcome <;> simp [retainedPhysicalLetter, reflectUppercase_involutive]
  rw [back]

/-! ## Physical count on the reflected input -/

/-- **Report and physical count together.** On the original recursive calibrated-or-terminal-twin
domain of a detected root, the reflected input's report entry at that root is the reflected
original entry, and its executable source-coordinate pair count equals the original's (both equal
the physical count of the configuration and of its mirror). -/
theorem reflectInput_rootEntry_and_count
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.detectedMultiCenterMolecule.Center)
    (domain : LocalizedRecursiveAuxiliaryPhysicalDomain.RecursiveAuxiliaryPhysicalDomain
      input.certified cfg root)
    (outcome : Option LocalizedAuxiliaryLabel) :
    ((root.1.val, outcome.map (retainedPhysicalLetter true)) ∈ analyze (reflectInput input) ↔
        (root.1.val, outcome) ∈ analyze input) ∧
      FinitePhysicalBranchTransport.computedPairCount
          (LocalizedActualPhysicalBranchDecision.actualCanonicalMolecule
            (reflectedCertified input.certified))
          (LocalizedActualPhysicalBranchDecision.coordinateCfg
            (reflectedCertified input.certified)) ⟨root.1, root.2⟩ =
        FinitePhysicalBranchTransport.computedPairCount
          (LocalizedActualPhysicalBranchDecision.actualCanonicalMolecule input.certified)
          (LocalizedActualPhysicalBranchDecision.coordinateCfg input.certified) ⟨root.1, root.2⟩ :=
  ⟨mem_analyze_reflectInput_map_iff singleBonded _ outcome,
    computedPairCount_coordinateCfg_reflectInput input.certified cfg root domain⟩

end

end TetraStereo.OneCenter.LocalizedReferenceInputMirrorCovariance

assert_kernel_only TetraStereo.OneCenter.LocalizedReferenceInputMirrorCovariance.outcomeAt_reflect
assert_kernel_only TetraStereo.OneCenter.LocalizedReferenceInputMirrorCovariance.stateMap_mirroredState
assert_kernel_only
  TetraStereo.OneCenter.LocalizedReferenceInputMirrorCovariance.mirroredState_sourceRetainedModel
assert_kernel_only
  TetraStereo.OneCenter.LocalizedReferenceInputMirrorCovariance.referenceState_reflectInput
assert_kernel_only
  TetraStereo.OneCenter.LocalizedReferenceInputMirrorCovariance.referenceState_reflectInput_mapOcc
assert_kernel_only
  TetraStereo.OneCenter.LocalizedReferenceInputMirrorCovariance.descriptorMap_reflectInput
assert_kernel_only
  TetraStereo.OneCenter.LocalizedReferenceInputMirrorCovariance.mem_analyze_reflectInput_iff
assert_kernel_only
  TetraStereo.OneCenter.LocalizedReferenceInputMirrorCovariance.reflectInput_rootEntry_and_count
