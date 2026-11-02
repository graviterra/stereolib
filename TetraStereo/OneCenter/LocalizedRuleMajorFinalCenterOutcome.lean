import TetraStereo.OneCenter.LocalizedRuleMajorGeometricExecution
import TetraStereo.OneCenter.LocalizedRuleMajorIndependentPairCount
import TetraStereo.OneCenter.DeclarativeCIPCompleteRootDescriptor
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Given available canonical points with nonzero determinant, the generated own-state endpoint
is exactly the independent complete-root judgment whenever the complete molecular keys are
injective, and both evaluators refuse when they are not. The tracked pseudo count is eliminated
using the independently proved prior-pair-count bridge. This endpoint makes no physical
enantiomorphism claim. -/

namespace TetraStereo.OneCenter.LocalizedRuleMajorReference

open CertifiedLocalizedCIPInput DeclarativeCIP
noncomputable section
open scoped Classical

namespace GeneratedRuleMajorFrameComparisonData

variable {input : Input} {center : input.certified.TetrahedralCenter}

private theorem executable_eq_referenceState
    (input : Input) (center : input.certified.TetrahedralCenter) :
    input.certified.ruleMajorDescriptorExec? (generatedTarget input center)
        (input.certified.localizedDependencyView (referenceState input)
          (generatedTarget input center)) =
      referenceState input (generatedTarget input center) := by
  calc
    input.certified.ruleMajorDescriptorExec? (generatedTarget input center)
        (input.certified.localizedDependencyView (referenceState input)
          (generatedTarget input center)) =
      input.certified.ruleMajorDescriptor? (generatedTarget input center)
        (input.certified.localizedDependencyView (referenceState input)
          (generatedTarget input center)) :=
      input.certified.ruleMajorDescriptorExec?_eq _ _
    _ = referenceState input (generatedTarget input center) :=
      reference_fixed input (generatedTarget input center)

/-- An actual own-state descriptor exists with a given label exactly when that label satisfies
the independent complete-key ordering and geometry judgment. -/
theorem ruleMajor_exec_some_iff_root_judgment
    (input : Input) (center : input.certified.TetrahedralCenter)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (frames : GeneratedRuleMajorFrameComparisonData input center)
    (points : Fin 4 → CartesianPoint3)
    (pointsAvailable : ∀ index : Fin 4,
      input.certified.spatialPointAt?
        (input.certified.canonicalLigandAtom center index) = some (points index))
    (nonzero : CartesianPoint3.orientedVolume (points 0) (points 1)
      (points 2) (points 3) ≠ 0)
    (descriptor : LocalizedAuxiliaryLabel) :
    input.certified.ruleMajorDescriptorExec? (generatedTarget input center)
        (input.certified.localizedDependencyView (referenceState input)
          (generatedTarget input center)) = some descriptor ↔
      CompleteRootDescriptorJudgment frames.data.fullKey points descriptor := by
  by_cases distinct : Function.Injective frames.data.fullKey
  · obtain ⟨tracked, raw, _center, _frame, _frameMeaning, orderComputed,
      permutation, descending, _spatial, _pointsComputed, rational,
      execComputed, _stateComputed⟩ :=
        GeneratedRuleMajorFrameComparisonData.ruleMajor_geometric_execution input center singleBonded acyclic
          frames distinct points pointsAvailable nonzero
    have trackedCount := GeneratedRuleMajorFrameComparisonData.trackedCount_eq_independent
      (input := input) (center := center) frames singleBonded acyclic
      distinct tracked orderComputed
    let ligandOrder := tracked.highestFirst.map frames.ligandToSlot.symm
    have ligandOrderPerm : ligandOrder.Perm (List.finRange 4) :=
      (permutation.map _).trans (Rule4aTableBridge.finRange_map_perm _)
    have ligandOrderSorted : ligandOrder.Pairwise
        (fun left right => frames.data.fullKey right < frames.data.fullKey left) := by
      dsimp [ligandOrder]
      rw [List.pairwise_map]
      exact descending
    have ligandOrderRational : RationalTetrahedralDescriptor (ligandOrder.map points) raw := by
      dsimp [ligandOrder]
      simpa [GeneratedRuleMajorFrameComparisonData.canonicalPointAtSlot, List.map_map,
        Function.comp_def] using rational
    have generatedJudgment : CompleteRootDescriptorJudgment frames.data.fullKey points
        (classifyTetrahedralRSPseudo raw tracked.pseudoComparisons) := by
      refine ⟨ligandOrder, raw, ligandOrderPerm, ligandOrderSorted, ligandOrderRational, ?_⟩
      rw [trackedCount]
    constructor
    · intro actual
      have descriptorEq : descriptor =
          classifyTetrahedralRSPseudo raw tracked.pseudoComparisons :=
        Option.some.inj (actual.symm.trans execComputed)
      simpa [descriptorEq] using generatedJudgment
    · intro judgment
      have descriptorEq := completeRootDescriptorJudgment_unique generatedJudgment judgment
      rw [← descriptorEq]
      exact execComputed
  · have execNone : input.certified.ruleMajorDescriptorExec?
        (generatedTarget input center)
        (input.certified.localizedDependencyView (referenceState input)
          (generatedTarget input center)) = none := by
      exact (GeneratedRuleMajorFrameComparisonData.ruleMajor_geometric_refusal_of_not_injective input center
        singleBonded acyclic frames distinct).2.1
    have noJudgment : ¬ CompleteRootDescriptorJudgment frames.data.fullKey points descriptor :=
      fun judgment => distinct
        (completeRootDescriptorJudgment_injective judgment)
    simp [execNone, noJudgment]

/-- The generated own-state label obeys the same complete independent judgment iff. -/
theorem ruleMajor_referenceState_some_iff_root_judgment
    (input : Input) (center : input.certified.TetrahedralCenter)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (frames : GeneratedRuleMajorFrameComparisonData input center)
    (points : Fin 4 → CartesianPoint3)
    (pointsAvailable : ∀ index : Fin 4,
      input.certified.spatialPointAt?
        (input.certified.canonicalLigandAtom center index) = some (points index))
    (nonzero : CartesianPoint3.orientedVolume (points 0) (points 1)
      (points 2) (points 3) ≠ 0)
    (descriptor : LocalizedAuxiliaryLabel) :
    referenceState input (generatedTarget input center) = some descriptor ↔
      CompleteRootDescriptorJudgment frames.data.fullKey points descriptor := by
  rw [← executable_eq_referenceState input center]
  exact GeneratedRuleMajorFrameComparisonData.ruleMajor_exec_some_iff_root_judgment input center singleBonded acyclic
    frames points pointsAvailable nonzero descriptor

/-- The actual rule-major sorter refuses exactly when complete independent ligand keys collide. -/
theorem ruleMajor_exec_none_iff_not_injective
    (input : Input) (center : input.certified.TetrahedralCenter)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (frames : GeneratedRuleMajorFrameComparisonData input center)
    (points : Fin 4 → CartesianPoint3)
    (pointsAvailable : ∀ index : Fin 4,
      input.certified.spatialPointAt?
        (input.certified.canonicalLigandAtom center index) = some (points index))
    (nonzero : CartesianPoint3.orientedVolume (points 0) (points 1)
      (points 2) (points 3) ≠ 0) :
    input.certified.ruleMajorDescriptorExec? (generatedTarget input center)
        (input.certified.localizedDependencyView (referenceState input)
          (generatedTarget input center)) = none ↔
      ¬ Function.Injective frames.data.fullKey := by
  constructor
  · intro refused distinct
    obtain ⟨tracked, _raw, _, _, _, _, _, _, _, _, _, execComputed, _⟩ :=
      GeneratedRuleMajorFrameComparisonData.ruleMajor_geometric_execution input center singleBonded acyclic frames
        distinct points pointsAvailable nonzero
    rw [refused] at execComputed
    cases execComputed
  · intro notDistinct
    exact (GeneratedRuleMajorFrameComparisonData.ruleMajor_geometric_refusal_of_not_injective input center
      singleBonded acyclic frames notDistinct).2.1

/-- The own fixed-point state refuses at exactly the same noninjectivity boundary. -/
theorem ruleMajor_referenceState_none_iff_not_injective
    (input : Input) (center : input.certified.TetrahedralCenter)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (frames : GeneratedRuleMajorFrameComparisonData input center)
    (points : Fin 4 → CartesianPoint3)
    (pointsAvailable : ∀ index : Fin 4,
      input.certified.spatialPointAt?
        (input.certified.canonicalLigandAtom center index) = some (points index))
    (nonzero : CartesianPoint3.orientedVolume (points 0) (points 1)
      (points 2) (points 3) ≠ 0) :
    referenceState input (generatedTarget input center) = none ↔
      ¬ Function.Injective frames.data.fullKey := by
  rw [← executable_eq_referenceState input center]
  exact GeneratedRuleMajorFrameComparisonData.ruleMajor_exec_none_iff_not_injective input center singleBonded acyclic
    frames points pointsAvailable nonzero

end GeneratedRuleMajorFrameComparisonData

/-- A canonical generated frame package is available for every certified tetrahedral center. -/
noncomputable def generatedFrameComparison (input : Input)
    (center : input.certified.TetrahedralCenter)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic) :
    GeneratedRuleMajorFrameComparisonData input center :=
  Classical.choice (generated_frame_comparison input center singleBonded acyclic)

/-- Uniform detected-center facade for the actual callback and independent complete-root
judgment. -/
theorem generated_ruleMajor_exec_some_iff_root_judgment
    (input : Input) (center : input.certified.TetrahedralCenter)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (points : Fin 4 → CartesianPoint3)
    (pointsAvailable : ∀ index : Fin 4,
      input.certified.spatialPointAt?
        (input.certified.canonicalLigandAtom center index) = some (points index))
    (nonzero : CartesianPoint3.orientedVolume (points 0) (points 1)
      (points 2) (points 3) ≠ 0)
    (descriptor : LocalizedAuxiliaryLabel) :
    input.certified.ruleMajorDescriptorExec? (generatedTarget input center)
        (input.certified.localizedDependencyView (referenceState input)
          (generatedTarget input center)) = some descriptor ↔
      CompleteRootDescriptorJudgment
        (generatedFrameComparison input center singleBonded acyclic).data.fullKey
        points descriptor := by
  exact GeneratedRuleMajorFrameComparisonData.ruleMajor_exec_some_iff_root_judgment
    input center singleBonded acyclic (generatedFrameComparison input center singleBonded acyclic)
    points pointsAvailable nonzero descriptor

/-- Uniform detected-center facade for the generated own-state readback. -/
theorem generated_referenceState_some_iff_root_judgment
    (input : Input) (center : input.certified.TetrahedralCenter)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (points : Fin 4 → CartesianPoint3)
    (pointsAvailable : ∀ index : Fin 4,
      input.certified.spatialPointAt?
        (input.certified.canonicalLigandAtom center index) = some (points index))
    (nonzero : CartesianPoint3.orientedVolume (points 0) (points 1)
      (points 2) (points 3) ≠ 0)
    (descriptor : LocalizedAuxiliaryLabel) :
    referenceState input (generatedTarget input center) = some descriptor ↔
      CompleteRootDescriptorJudgment
        (generatedFrameComparison input center singleBonded acyclic).data.fullKey
        points descriptor := by
  exact GeneratedRuleMajorFrameComparisonData.ruleMajor_referenceState_some_iff_root_judgment
    input center singleBonded acyclic (generatedFrameComparison input center singleBonded acyclic)
    points pointsAvailable nonzero descriptor

/-- Uniform detected-center refusal iff for the actual generated complete keys are not injective. -/
theorem generated_ruleMajor_exec_none_iff_not_injective
    (input : Input) (center : input.certified.TetrahedralCenter)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (points : Fin 4 → CartesianPoint3)
    (pointsAvailable : ∀ index : Fin 4,
      input.certified.spatialPointAt?
        (input.certified.canonicalLigandAtom center index) = some (points index))
    (nonzero : CartesianPoint3.orientedVolume (points 0) (points 1)
      (points 2) (points 3) ≠ 0) :
    input.certified.ruleMajorDescriptorExec? (generatedTarget input center)
        (input.certified.localizedDependencyView (referenceState input)
          (generatedTarget input center)) = none ↔
      ¬ Function.Injective
        (generatedFrameComparison input center singleBonded acyclic).data.fullKey := by
  exact GeneratedRuleMajorFrameComparisonData.ruleMajor_exec_none_iff_not_injective
    input center singleBonded acyclic (generatedFrameComparison input center singleBonded acyclic)
    points pointsAvailable nonzero

/-- Uniform detected-center own-state refusal iff for the actual generated complete keys are not
injective. -/
theorem generated_referenceState_none_iff_not_injective
    (input : Input) (center : input.certified.TetrahedralCenter)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (points : Fin 4 → CartesianPoint3)
    (pointsAvailable : ∀ index : Fin 4,
      input.certified.spatialPointAt?
        (input.certified.canonicalLigandAtom center index) = some (points index))
    (nonzero : CartesianPoint3.orientedVolume (points 0) (points 1)
      (points 2) (points 3) ≠ 0) :
    referenceState input (generatedTarget input center) = none ↔
      ¬ Function.Injective
        (generatedFrameComparison input center singleBonded acyclic).data.fullKey := by
  exact GeneratedRuleMajorFrameComparisonData.ruleMajor_referenceState_none_iff_not_injective
    input center singleBonded acyclic (generatedFrameComparison input center singleBonded acyclic)
    points pointsAvailable nonzero

/-- All-center outcome facade. For every certified detected tetrahedral center with available
canonical points and nonzero determinant, the own-state and executable labels are exactly the
independent complete-root judgment when present; both refuse exactly on a complete-key collision.
The returned label is lowercase exactly when the independent complete prior-pair count is one.
Each center's frame package is constructed from the generated evaluator, and each center receives
its own physical coordinate witnesses. -/
theorem generated_all_centers_complete_outcome
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (points : input.certified.TetrahedralCenter → Fin 4 → CartesianPoint3)
    (pointsAvailable : ∀ center index,
      input.certified.spatialPointAt?
        (input.certified.canonicalLigandAtom center index) = some (points center index))
    (nonzero : ∀ center : input.certified.TetrahedralCenter,
      CartesianPoint3.orientedVolume (points center 0) (points center 1)
        (points center 2) (points center 3) ≠ 0) :
    ∀ center : input.certified.TetrahedralCenter, ∀ descriptor : LocalizedAuxiliaryLabel,
      (input.certified.ruleMajorDescriptorExec? (generatedTarget input center)
          (input.certified.localizedDependencyView (referenceState input)
            (generatedTarget input center)) = some descriptor ↔
        CompleteRootDescriptorJudgment
          (generatedFrameComparison input center singleBonded acyclic).data.fullKey
          (points center) descriptor) ∧
      (referenceState input (generatedTarget input center) = some descriptor ↔
        CompleteRootDescriptorJudgment
          (generatedFrameComparison input center singleBonded acyclic).data.fullKey
          (points center) descriptor) ∧
      ((input.certified.ruleMajorDescriptorExec? (generatedTarget input center)
          (input.certified.localizedDependencyView (referenceState input)
            (generatedTarget input center)) = some descriptor ∧
        referenceState input (generatedTarget input center) = some descriptor) →
        (descriptor.IsLowercase ↔
          completeRule5PairCount
            (generatedFrameComparison input center singleBonded acyclic).data.fullKey = 1)) ∧
      ((input.certified.ruleMajorDescriptorExec? (generatedTarget input center)
          (input.certified.localizedDependencyView (referenceState input)
            (generatedTarget input center)) = none ∧
        referenceState input (generatedTarget input center) = none) ↔
        ¬ Function.Injective
          (generatedFrameComparison input center singleBonded acyclic).data.fullKey) := by
  intro center descriptor
  let frames := generatedFrameComparison input center singleBonded acyclic
  have execIff := GeneratedRuleMajorFrameComparisonData.ruleMajor_exec_some_iff_root_judgment input center
    singleBonded acyclic frames (points center) (pointsAvailable center) (nonzero center)
    descriptor
  have stateIff := GeneratedRuleMajorFrameComparisonData.ruleMajor_referenceState_some_iff_root_judgment input center
    singleBonded acyclic frames (points center) (pointsAvailable center) (nonzero center)
    descriptor
  have execNone := GeneratedRuleMajorFrameComparisonData.ruleMajor_exec_none_iff_not_injective input center
    singleBonded acyclic frames (points center) (pointsAvailable center) (nonzero center)
  have stateNone := GeneratedRuleMajorFrameComparisonData.ruleMajor_referenceState_none_iff_not_injective input center
    singleBonded acyclic frames (points center) (pointsAvailable center) (nonzero center)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [frames] using execIff
  · simpa [frames] using stateIff
  · intro success
    have judgment := execIff.mp success.1
    exact (completeRootDescriptorJudgment_lowercase_iff judgment)
  · constructor
    · rintro ⟨execRefused, _stateRefused⟩
      exact execNone.mp execRefused
    · intro notDistinct
      exact ⟨execNone.mpr notDistinct, stateNone.mpr notDistinct⟩

end
end TetraStereo.OneCenter.LocalizedRuleMajorReference

assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFrameComparisonData.ruleMajor_exec_some_iff_root_judgment
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFrameComparisonData.ruleMajor_referenceState_some_iff_root_judgment
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFrameComparisonData.ruleMajor_exec_none_iff_not_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFrameComparisonData.ruleMajor_referenceState_none_iff_not_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.generatedFrameComparison
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.generated_ruleMajor_exec_some_iff_root_judgment
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.generated_referenceState_some_iff_root_judgment
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.generated_ruleMajor_exec_none_iff_not_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.generated_referenceState_none_iff_not_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.generated_all_centers_complete_outcome
