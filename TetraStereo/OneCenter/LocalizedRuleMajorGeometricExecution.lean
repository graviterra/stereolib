import TetraStereo.OneCenter.LocalizedRuleMajorActualSortCompleteness
import TetraStereo.OneCenter.LocalizedRuleMajorReferencePipeline
import TetraStereo.OneCenter.LocalizedNoDoubleDescriptorExecutable
import TetraStereo.OneCenter.LocalizedTetrahedralPermutationExistence
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Physical coordinates now drive the revised evaluator's generated Rule-5 order.  The input
contains only canonical per-ligand coordinate lookups and a nonzero canonical determinant;
the generated frame, center recognition, actual safe sort, cursor reads, and descriptor output
are derived.  The pseudo-comparison count remains the count carried by the actual tracked sort. -/

namespace TetraStereo.OneCenter.LocalizedRuleMajorReference

open CertifiedLocalizedCIPInput DeclarativeCIP
noncomputable section
open scoped Classical

namespace GeneratedRuleMajorFrameComparisonData

variable {input : Input} {center : input.certified.TetrahedralCenter}

/-- The canonical coordinate of a runtime frame slot, transported by the generated frame's
proved slot-to-ligand bijection. -/
def canonicalPointAtSlot (frames : GeneratedRuleMajorFrameComparisonData input center)
    (points : Fin 4 → CartesianPoint3) (slot : Fin 4) : CartesianPoint3 :=
  points (frames.ligandToSlot.symm slot)

private theorem cursor_spatialPoint_of_canonicalPoints
    (frames : GeneratedRuleMajorFrameComparisonData input center)
    (points : Fin 4 → CartesianPoint3)
    (pointsAvailable : ∀ index : Fin 4,
      input.certified.spatialPointAt?
        (input.certified.canonicalLigandAtom center index) = some (points index))
    (slot : Fin 4) :
    input.certified.localizedRerootCursorSpatialPoint? (frames.frame.cursorAt slot) =
      some (frames.canonicalPointAtSlot points slot) := by
  have current : (frames.frame.cursorAt slot).occurrence.1.node.current? =
      some (input.certified.canonicalLigandAtom center (frames.ligandToSlot.symm slot)) := by
    rw [frames.cursorAt slot]
    simp [localizedLigandRootCursor_node, localizedLigandRootNode]
  simp [localizedRerootCursorSpatialPoint?, current, canonicalPointAtSlot,
    pointsAvailable (frames.ligandToSlot.symm slot)]

private theorem mapM_cursor_spatialPoint_eq_some
    (frames : GeneratedRuleMajorFrameComparisonData input center)
    (points : Fin 4 → CartesianPoint3)
    (pointsAvailable : ∀ index : Fin 4,
      input.certified.spatialPointAt?
        (input.certified.canonicalLigandAtom center index) = some (points index)) :
    ∀ order : List (Fin 4),
      order.mapM (fun slot =>
        input.certified.localizedRerootCursorSpatialPoint? (frames.frame.cursorAt slot)) =
        some (order.map (frames.canonicalPointAtSlot points))
  | [] => rfl
  | slot :: order => by
      simp [List.mapM_cons, cursor_spatialPoint_of_canonicalPoints frames points
        pointsAvailable slot, mapM_cursor_spatialPoint_eq_some frames points
        pointsAvailable order]

private theorem mapped_frameOrder_is_permutation
    (frames : GeneratedRuleMajorFrameComparisonData input center)
    {order : List (Fin 4)}
    (permutation : order.Perm (List.finRange 4)) :
    (order.map frames.ligandToSlot.symm).Perm (List.finRange 4) := by
  exact (permutation.map frames.ligandToSlot.symm).trans
    (Rule4aTableBridge.finRange_map_perm frames.ligandToSlot.symm)

/-- Successful geometric execution of the own-state Rule-5 evaluator. Independent-key
injectivity proves the actual safe sort succeeds and supplies its descending order. Canonical
coordinate lookups and their nonzero determinant then make the evaluator's mapM and descriptor
read succeed. The emitted count is exactly the count carried by the actual tracked sort. -/
theorem ruleMajor_geometric_execution
    (input : Input) (center : input.certified.TetrahedralCenter)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (frames : GeneratedRuleMajorFrameComparisonData input center)
    (distinct : Function.Injective frames.data.fullKey)
    (points : Fin 4 → CartesianPoint3)
    (pointsAvailable : ∀ index : Fin 4,
      input.certified.spatialPointAt?
        (input.certified.canonicalLigandAtom center index) = some (points index))
    (nonzero : CartesianPoint3.orientedVolume (points 0) (points 1)
      (points 2) (points 3) ≠ 0) :
    ∃ tracked raw,
      input.certified.localizedOccurrenceDescriptorCenter?
          (generatedTarget input center) = some center ∧
        input.certified.localizedNoDoubleFourLigandFrameExec?
          (generatedTarget input center) = some frames.frame ∧
        input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
          (generatedTarget input center) frames.frame ∧
        safeTrackedOrderOrderedExecOf frames.actualCallback = some tracked ∧
        tracked.highestFirst.Perm (List.finRange 4) ∧
        tracked.highestFirst.Pairwise (fun left right =>
          frames.data.fullKey (frames.ligandToSlot.symm right) <
            frames.data.fullKey (frames.ligandToSlot.symm left)) ∧
        (∀ slot : Fin 4,
          input.certified.localizedRerootCursorSpatialPoint?
              (frames.frame.cursorAt slot) =
            some (frames.canonicalPointAtSlot points slot)) ∧
        tracked.highestFirst.mapM (fun slot =>
          input.certified.localizedRerootCursorSpatialPoint? (frames.frame.cursorAt slot)) =
            some (tracked.highestFirst.map (frames.canonicalPointAtSlot points)) ∧
        RationalTetrahedralDescriptor
          (tracked.highestFirst.map (frames.canonicalPointAtSlot points)) raw ∧
        input.certified.ruleMajorDescriptorExec?
          (generatedTarget input center)
          (input.certified.localizedDependencyView
            (referenceState input) (generatedTarget input center)) =
          some (classifyTetrahedralRSPseudo raw tracked.pseudoComparisons) ∧
        referenceState input (generatedTarget input center) =
          some (classifyTetrahedralRSPseudo raw tracked.pseudoComparisons) := by
  let target := generatedTarget input center
  let view := input.certified.localizedDependencyView (referenceState input) target
  have targetCurrent : target.1.node.current? = some center.1 := by
    change (ActualReaderPhysicalBranchInverse.topTarget input center).1.node.current? = some center.1
    exact ActualReaderPhysicalBranchInverse.topTarget_current input center
  have centerReal : input.certified.RealTetrahedralCenterNode target.1.node center :=
    ⟨input.certified.carrierOccurrence_provenance_real singleBonded acyclic target,
      targetCurrent⟩
  have centerComputed : input.certified.localizedOccurrenceDescriptorCenter? target =
      some center :=
    (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff target center).2 centerReal
  have frameComputed : input.certified.localizedNoDoubleFourLigandFrameExec? target =
      some frames.frame := by
    rw [input.certified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
    exact frames.frameComputed
  have frameDerived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      target frames.frame :=
    input.certified.localizedOccurrenceFourLigandFrame?_sound target frames.frame frames.frameComputed
  obtain ⟨tracked, orderComputed, permutation, descending⟩ := frames.safeOrder_exists distinct
  have spatial : ∀ slot : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint? (frames.frame.cursorAt slot) =
        some (frames.canonicalPointAtSlot points slot) :=
    cursor_spatialPoint_of_canonicalPoints frames points pointsAvailable
  have pointsComputed : tracked.highestFirst.mapM (fun slot =>
      input.certified.localizedRerootCursorSpatialPoint? (frames.frame.cursorAt slot)) =
        some (tracked.highestFirst.map (frames.canonicalPointAtSlot points)) :=
    mapM_cursor_spatialPoint_eq_some frames points pointsAvailable tracked.highestFirst
  have actualOrderComputed : safeTrackedOrderOrderedExecOf
      (input.certified.compareRuleMajorOccurrenceExecAt? target view frames.frame) = some tracked := by
    simpa [GeneratedRuleMajorFrameComparisonData.actualCallback, target, view] using orderComputed
  have mappedPermutation : (tracked.highestFirst.map frames.ligandToSlot.symm).Perm
      (List.finRange 4) :=
    mapped_frameOrder_is_permutation frames permutation
  obtain ⟨raw, rawMeaning⟩ := rationalTetrahedralDescriptor_exists_of_permutation
    points (tracked.highestFirst.map frames.ligandToSlot.symm) mappedPermutation nonzero
  have pointsOrderEq :
      tracked.highestFirst.map (frames.canonicalPointAtSlot points) =
        (tracked.highestFirst.map frames.ligandToSlot.symm).map points := by
    simp [canonicalPointAtSlot, List.map_map]
  have rational : RationalTetrahedralDescriptor
      (tracked.highestFirst.map (frames.canonicalPointAtSlot points)) raw := by
    rw [pointsOrderEq]
    exact rawMeaning
  have evidenceComputed : input.certified.ruleMajorSpatialEvidenceExec? target view =
      some { center := center, frame := frames.frame, tracked := tracked, points :=
        tracked.highestFirst.map (frames.canonicalPointAtSlot points) } := by
    unfold CertifiedLocalizedCIPInput.ruleMajorSpatialEvidenceExec?
    simp [centerComputed, frameComputed, actualOrderComputed, pointsComputed]
  have rawComputed : descriptorOfPriorityOrderedPoints?
      (tracked.highestFirst.map (frames.canonicalPointAtSlot points)) = some raw :=
    (descriptorOfPriorityOrderedPoints?_eq_some_iff _ _).2 rational
  have descriptorComputed : input.certified.ruleMajorDescriptorExec? target view =
      some (classifyTetrahedralRSPseudo raw tracked.pseudoComparisons) := by
    simp [CertifiedLocalizedCIPInput.ruleMajorDescriptorExec?, evidenceComputed, rawComputed]
  have stateComputed : referenceState input target =
      some (classifyTetrahedralRSPseudo raw tracked.pseudoComparisons) := by
    calc
      referenceState input target =
          input.certified.ruleMajorDescriptor? target view :=
        (reference_fixed input target).symm
      _ = input.certified.ruleMajorDescriptorExec? target view :=
        (input.certified.ruleMajorDescriptorExec?_eq target view).symm
      _ = some (classifyTetrahedralRSPseudo raw tracked.pseudoComparisons) :=
        descriptorComputed
  refine ⟨tracked, raw, centerComputed, frameComputed, frameDerived, orderComputed,
    permutation, descending, spatial, pointsComputed, rational, ?_, stateComputed⟩
  simpa [target, view] using descriptorComputed

/-- Failure of independent-key injectivity is the evaluator's actual safe-sort refusal. It
propagates through the generated descriptor and its own fixed-point state. -/
theorem ruleMajor_geometric_refusal_of_not_injective
    (input : Input) (center : input.certified.TetrahedralCenter)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (frames : GeneratedRuleMajorFrameComparisonData input center)
    (notDistinct : ¬ Function.Injective frames.data.fullKey) :
    safeTrackedOrderOrderedExecOf frames.actualCallback = none ∧
      input.certified.ruleMajorDescriptorExec?
        (generatedTarget input center)
        (input.certified.localizedDependencyView (referenceState input)
          (generatedTarget input center)) = none ∧
      referenceState input (generatedTarget input center) = none := by
  let target := generatedTarget input center
  let view := input.certified.localizedDependencyView (referenceState input) target
  have targetCurrent : target.1.node.current? = some center.1 := by
    change (ActualReaderPhysicalBranchInverse.topTarget input center).1.node.current? = some center.1
    exact ActualReaderPhysicalBranchInverse.topTarget_current input center
  have centerReal : input.certified.RealTetrahedralCenterNode target.1.node center :=
    ⟨input.certified.carrierOccurrence_provenance_real singleBonded acyclic target,
      targetCurrent⟩
  have centerComputed : input.certified.localizedOccurrenceDescriptorCenter? target =
      some center :=
    (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff target center).2 centerReal
  have frameComputed : input.certified.localizedNoDoubleFourLigandFrameExec? target =
      some frames.frame := by
    rw [input.certified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
    exact frames.frameComputed
  have orderRefused := frames.safeOrder_eq_none_of_not_injective notDistinct
  have actualOrderRefused : safeTrackedOrderOrderedExecOf
      (input.certified.compareRuleMajorOccurrenceExecAt? target view frames.frame) = none := by
    simpa [GeneratedRuleMajorFrameComparisonData.actualCallback] using orderRefused
  have evidenceRefused : input.certified.ruleMajorSpatialEvidenceExec? target view = none := by
    unfold CertifiedLocalizedCIPInput.ruleMajorSpatialEvidenceExec?
    simp [centerComputed, frameComputed, actualOrderRefused]
  have descriptorRefused : input.certified.ruleMajorDescriptorExec? target view = none := by
    simp [CertifiedLocalizedCIPInput.ruleMajorDescriptorExec?, evidenceRefused]
  have stateRefused : referenceState input target = none := by
    calc
      referenceState input target = input.certified.ruleMajorDescriptor? target view :=
        (reference_fixed input target).symm
      _ = input.certified.ruleMajorDescriptorExec? target view :=
        (input.certified.ruleMajorDescriptorExec?_eq target view).symm
      _ = none := descriptorRefused
  refine ⟨orderRefused, ?_, ?_⟩
  · simpa [target, view] using descriptorRefused
  · exact stateRefused

end GeneratedRuleMajorFrameComparisonData
end
end TetraStereo.OneCenter.LocalizedRuleMajorReference

assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFrameComparisonData.canonicalPointAtSlot
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFrameComparisonData.ruleMajor_geometric_execution
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFrameComparisonData.ruleMajor_geometric_refusal_of_not_injective
