import TetraStereo.OneCenter.LocalizedRuleMajorBinaryPriorClasses
import TetraStereo.OneCenter.LocalizedRuleMajorActualSortCompleteness
import TetraStereo.OneCenter.LocalizedRuleMajorFinalCenterOutcome
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! A geometry-conditional execution bridge for arbitrary actual target occurrences. The
contextual comparison data is supplied independently of frame geometry; coordinate availability
is existential in the result, so missing or degenerate coordinates do not become assumptions of
the universal endpoint. The adapter also derives the tracked pair count from the complete keys;
constructing its contextual comparison-data bundle is a separate obligation. -/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open DeclarativeCIP Rule4aTableBridge
noncomputable section
open scoped Classical

/-- Actual comparisons and independent full keys for the four frame slots at one arbitrary
target. The caller derives these fields from the contextual stage family. -/
structure ContextDescriptorExecutionData (input : CertifiedLocalizedCIPInput)
    {fuel : Nat} (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) where
  center : input.TetrahedralCenter
  centerComputed : input.localizedOccurrenceDescriptorCenter? target = some center
  frame : input.LocalizedOccurrenceFourLigandFrame fuel
  frameComputed : input.localizedNoDoubleFourLigandFrameExec? target = some frame
  compounds : Fin 4 → input.LocalizedRerootCompoundRule45Key
  keys : Fin 4 → CompleteLigandRule5Key
  callbackEq : (fun left right => input.compareRuleMajorOccurrenceExecAt?
      target view frame left right) = compoundActualCompareAt input compounds
  fullOrdering : ∀ left right,
    (input.compareLocalizedRerootCompoundThroughRule5
      (compounds left) (compounds right)).ordering = compare (keys left) (keys right)
  priorComparison : ∀ left right,
    input.compareLocalizedRerootCompoundRule4bcKeys
      (compounds left).prior (compounds right).prior =
      compare (ofLex (keys left)).1 (ofLex (keys right)).1
  shaped : ∀ index, input.RuleMajorReadingShape (compounds index)

namespace ContextDescriptorExecutionData

variable {input : CertifiedLocalizedCIPInput} {fuel : Nat}
  {target : input.LocalizedCIPOccurrence fuel}
  {view : input.LocalizedDependencyView target}
  (data : input.ContextDescriptorExecutionData target view)

private theorem compounds_strict (injective : Function.Injective data.keys) :
    input.CompoundKeyOffDiagonalStrict data.compounds := by
  intro left right different equal
  have comparison := data.fullOrdering left right
  have keyCompare : compare (data.keys left) (data.keys right) = .eq := by
    rw [← comparison, input.compareLocalizedRerootCompoundThroughRule5_ordering]
    exact equal
  have keyEq := (completeLigandRule5Key_compare_eq_iff _ _).mp keyCompare
  exact different (injective keyEq)

private theorem keyCompare_rank (left right : Fin 4) :
    compare (data.keys left) (data.keys right) =
      compare (keyRank data.keys left) (keyRank data.keys right) := by
  have strict : compare (data.keys left) (data.keys right) = .lt ↔
      keyRank data.keys left < keyRank data.keys right := by
    rw [completeLigandRule5Key_compare_lt_iff,
      keyRank_lt_iff_without_injectivity]
  have tie : compare (data.keys left) (data.keys right) = .eq ↔
      keyRank data.keys left = keyRank data.keys right := by
    rw [completeLigandRule5Key_compare_eq_iff,
      keyRank_eq_iff_without_injectivity]
  exact eq_compare_of_iff _ _ _ strict tie

private theorem priorCount_eq_complete
    (injective : Function.Injective data.keys) :
    sourceEnantiomorphicPairCount (compoundPriorTieRelation input data.compounds) =
      completeRule5PairCount data.keys := by
  have strict := compounds_strict data injective
  have priorTie : ∀ left right,
      compoundPriorTieRelation input data.compounds left right ↔
        CompletePriorPair data.keys left right := by
    intro left right
    unfold compoundPriorTieRelation priorKeyTie CompletePriorPair
    rw [data.priorComparison left right, completeLigandPriorKey_compare_eq_iff]
  rw [sourceEnantiomorphicPairCount_congr_of_forall _ _ priorTie]
  rfl

/-- The actual tracked sorter counts exactly the independent complete-key prior pairs once the
actual compound shape and complete comparisons are supplied. -/
theorem trackedCount_eq_complete
    (injective : Function.Injective data.keys)
    (tracked : TrackedLocalizedLigandOrder)
    (computed : safeTrackedOrderOrderedExecOf
      (input.compareRuleMajorOccurrenceExecAt? target view data.frame) = some tracked) :
    tracked.pseudoComparisons = completeRule5PairCount data.keys := by
  have strict := compounds_strict data injective
  obtain ⟨maxTwo, mirror⟩ := input.ruleMajor_priorTie_dataCore data.compounds data.shaped strict
  have callbackEq :
      input.compareRuleMajorOccurrenceExecAt? target view data.frame =
        compoundActualCompareAt input data.compounds := data.callbackEq
  rw [callbackEq, safeTrackedOrderOrderedExecOf_eq] at computed
  obtain ⟨result, sortComputed, _, _, count⟩ :=
    sortFourLocalizedLigandsTracked_actualCompound_sourcePairFidelity input data.compounds
      strict maxTwo mirror
  have same : result = tracked := by
    have r1 : sortFourLocalizedLigandsTracked (compoundActualCompareAt input data.compounds) = some result := sortComputed
    have r2 : sortFourLocalizedLigandsTracked (compoundActualCompareAt input data.compounds) = some tracked := by
      unfold safeTrackedOrderOf at computed
      cases hsort : sortFourLocalizedLigandsTracked
          (compoundActualCompareAt input data.compounds) with
      | none => simp [hsort] at computed
      | some sorted =>
          simp only [hsort] at computed
          cases hcoherent : orderCoherentOf
              (compoundActualCompareAt input data.compounds) sorted.highestFirst with
          | false => simp [hcoherent] at computed
          | true =>
              simp [hcoherent] at computed
              cases computed
              rfl
    exact Option.some.inj (r1.symm.trans r2)
  subst tracked
  rw [count, priorCount_eq_complete data injective]

private theorem mapM_spatial_forall₂
    (frame : input.LocalizedOccurrenceFourLigandFrame fuel) :
    ∀ (order : List (Fin 4)) (points : List CartesianPoint3),
      order.mapM (fun slot => input.localizedRerootCursorSpatialPoint?
        (frame.cursorAt slot)) = some points →
      List.Forall₂ (fun slot point => input.localizedRerootCursorSpatialPoint?
        (frame.cursorAt slot) = some point) order points
  | [], points, h => by
      simp at h
      subst points
      exact .nil
  | slot :: order, points, h => by
      rw [List.mapM_cons] at h
      cases hp : input.localizedRerootCursorSpatialPoint? (frame.cursorAt slot) with
      | none => simp [hp] at h
      | some point =>
        cases ht : order.mapM (fun next => input.localizedRerootCursorSpatialPoint?
            (frame.cursorAt next)) with
        | none => simp [hp, ht] at h
        | some tail =>
          simp [hp, ht] at h
          subst points
          exact .cons hp (mapM_spatial_forall₂ frame order tail ht)

private theorem forall₂_exists_at_mem
    {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {x : α} (hx : x ∈ xs) :
    ∃ y, y ∈ ys ∧ R x y := by
  induction h with
  | nil => simp at hx
  | @cons a b as bs hab htail ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨b, List.mem_cons_self, hab⟩
    · obtain ⟨y, hy, hxy⟩ := ih hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hxy⟩

private theorem pairwise_mem_lt_injective
    {α : Type} [LinearOrder α] {xs : List (Fin 4)} {key : Fin 4 → α}
    (perm : xs.Perm (List.finRange 4))
    (sorted : xs.Pairwise (fun i j => key j < key i)) :
    Function.Injective key := by
  intro i j equal
  by_contra different
  have hi : i ∈ xs := perm.mem_iff.mpr (List.mem_finRange i)
  have hj : j ∈ xs := perm.mem_iff.mpr (List.mem_finRange j)
  have either := (List.Pairwise.forall (fun _ _ h => h.symm)
    (sorted.imp fun h => Or.inr h)) hi hj different
  rw [equal] at either
  exact either.elim (lt_irrefl _) (lt_irrefl _)

private theorem safeComputed_sort_facts
    (data : input.ContextDescriptorExecutionData target view)
    {tracked : TrackedLocalizedLigandOrder}
    (computed : safeTrackedOrderOrderedExecOf
      (input.compareRuleMajorOccurrenceExecAt? target view data.frame) = some tracked) :
    sortFourLocalizedLigandsTracked
        (input.compareRuleMajorOccurrenceExecAt? target view data.frame) = some tracked ∧
      orderCoherentOf (input.compareRuleMajorOccurrenceExecAt? target view data.frame)
        tracked.highestFirst = true := by
  rw [safeTrackedOrderOrderedExecOf_eq] at computed
  unfold safeTrackedOrderOf at computed
  cases hs : sortFourLocalizedLigandsTracked
      (input.compareRuleMajorOccurrenceExecAt? target view data.frame) with
  | none => simp [hs] at computed
  | some sorted =>
    simp only [hs] at computed
    cases hc : orderCoherentOf
        (input.compareRuleMajorOccurrenceExecAt? target view data.frame)
        sorted.highestFirst with
    | false => simp [hc] at computed
    | true =>
      simp [hc] at computed
      have eq : sorted = tracked := computed
      subst tracked
      exact ⟨rfl, hc⟩

private theorem sorted_keys_of_safe
    (data : input.ContextDescriptorExecutionData target view)
    {tracked : TrackedLocalizedLigandOrder}
    (coherent : orderCoherentOf
      (input.compareRuleMajorOccurrenceExecAt? target view data.frame)
      tracked.highestFirst = true) :
    tracked.highestFirst.Pairwise (fun left right => data.keys right < data.keys left) := by
  have pairwise := (orderCoherentOf_eq_true_iff _ _).mp coherent
  apply pairwise.imp
  intro left right witness
  obtain ⟨result, resultEq, ordering⟩ := witness
  have callbackEq := congrFun (congrFun data.callbackEq left) right
  rw [callbackEq] at resultEq
  simp only [compoundActualCompareAt, Option.some.injEq] at resultEq
  have recordOrdering := congrArg (fun result : ConstitutionalDescriptorHierarchyComparison =>
    result.ordering) resultEq.symm
  simp only [localizedOccurrenceRule45ComparisonRecord] at recordOrdering
  have fullOrder := data.fullOrdering left right
  have keyOrdering : compare (data.keys left) (data.keys right) = .gt := by
    rw [← fullOrder]
    exact recordOrdering.symm.trans ordering
  exact (completeLigandRule5Key_compare_gt_iff _ _).mp keyOrdering

private theorem all_spatial_points_of_mapM
    (frame : input.LocalizedOccurrenceFourLigandFrame fuel)
    {order : List (Fin 4)} {values : List CartesianPoint3}
    (permutation : order.Perm (List.finRange 4))
    (computed : order.mapM (fun slot => input.localizedRerootCursorSpatialPoint?
      (frame.cursorAt slot)) = some values) :
    ∃ points : Fin 4 → CartesianPoint3,
      (∀ slot, input.localizedRerootCursorSpatialPoint? (frame.cursorAt slot) =
        some (points slot)) ∧ order.map points = values := by
  have paired := mapM_spatial_forall₂ frame order values computed
  have available : ∀ slot, ∃ point,
      input.localizedRerootCursorSpatialPoint? (frame.cursorAt slot) = some point := by
    intro slot
    have member : slot ∈ order := permutation.mem_iff.mpr (List.mem_finRange slot)
    obtain ⟨point, _, hpoint⟩ := forall₂_exists_at_mem paired member
    exact ⟨point, hpoint⟩
  let points : Fin 4 → CartesianPoint3 := fun slot => Classical.choose (available slot)
  have hpoints slot := Classical.choose_spec (available slot)
  have mapped : ∀ order : List (Fin 4),
      order.mapM (fun slot => input.localizedRerootCursorSpatialPoint?
        (frame.cursorAt slot)) = some (order.map points) := by
    intro order
    induction order with
    | nil => rfl
    | cons slot rest ih =>
      rw [List.mapM_cons, hpoints slot, ih]
      rfl
  refine ⟨points, hpoints, ?_⟩
  exact Option.some.inj ((mapped order).symm.trans computed)

/-- Actual execution at any detected target succeeds with a descriptor exactly when the actual
frame supplies real coordinates and those coordinates satisfy the independent complete-root
judgment. The theorem makes no coordinate-availability or nondegeneracy assumption. -/
theorem exec_some_iff_completeRootJudgment
    (data : input.ContextDescriptorExecutionData target view)
    (descriptor : LocalizedAuxiliaryLabel) :
    input.ruleMajorDescriptorExec? target view = some descriptor ↔
      ∃ points : Fin 4 → CartesianPoint3,
        (∀ slot, input.localizedRerootCursorSpatialPoint? (data.frame.cursorAt slot) =
          some (points slot)) ∧
        CompleteRootDescriptorJudgment data.keys points descriptor := by
  constructor
  · intro actual
    have expanded := actual
    unfold CertifiedLocalizedCIPInput.ruleMajorDescriptorExec?
      CertifiedLocalizedCIPInput.ruleMajorSpatialEvidenceExec? at expanded
    rw [data.centerComputed, data.frameComputed] at expanded
    cases hs : safeTrackedOrderOrderedExecOf
        (input.compareRuleMajorOccurrenceExecAt? target view data.frame) with
    | none => simp [hs] at expanded
    | some tracked =>
      cases hp : tracked.highestFirst.mapM (fun slot =>
          input.localizedRerootCursorSpatialPoint? (data.frame.cursorAt slot)) with
      | none => simp [hs, hp] at expanded
      | some values =>
        cases hr : descriptorOfPriorityOrderedPoints? values with
        | none => simp [hs, hp, hr] at expanded
        | some raw =>
          simp [hs, hp, hr] at expanded
          have descriptorEq : descriptor = classifyTetrahedralRSPseudo raw
              tracked.pseudoComparisons := expanded.symm
          have sortFacts := safeComputed_sort_facts data hs
          have permutation := sortFourLocalizedLigandsTracked_perm
            (input.compareRuleMajorOccurrenceExecAt? target view data.frame)
            tracked sortFacts.1
          have pairwise := sorted_keys_of_safe data sortFacts.2
          have injective := pairwise_mem_lt_injective permutation pairwise
          have count := ContextDescriptorExecutionData.trackedCount_eq_complete
            data injective tracked hs
          obtain ⟨points, pointAvailable, pointsEq⟩ :=
            all_spatial_points_of_mapM data.frame permutation hp
          have rational := (descriptorOfPriorityOrderedPoints?_eq_some_iff _ _).1 hr
          have judgment : CompleteRootDescriptorJudgment data.keys points descriptor := by
            refine ⟨tracked.highestFirst, raw, permutation, pairwise, ?_, ?_⟩
            · simpa [pointsEq] using rational
            · rw [descriptorEq, count]
          exact ⟨points, pointAvailable, judgment⟩
  · intro witness
    rcases witness with ⟨points, pointAvailable, judgment⟩
    have keyInjective := completeRootDescriptorJudgment_injective judgment
    obtain ⟨order, raw, orderPerm, orderSorted, rational, descriptorEq⟩ := judgment
    have injective := keyInjective
    have strict := data.compounds_strict injective
    obtain ⟨maxTwo, mirror⟩ := input.ruleMajor_priorTie_dataCore data.compounds data.shaped strict
    let rank : Fin 4 → Nat := keyRank data.keys
    have rankInjective : Function.Injective rank := by
      intro left right equal
      exact injective ((keyRank_eq_iff_without_injectivity data.keys left right).mp equal)
    let callback := input.compareRuleMajorOccurrenceExecAt? target view data.frame
    have ranked : ∀ left right, left ≠ right → ∃ result,
        callback left right = some result ∧
          result.ordering = compare (rank left) (rank right) := by
      intro left right _
      have callbackEq := congrFun (congrFun data.callbackEq left) right
      refine ⟨localizedOccurrenceRule45ComparisonRecord
        (input.compareLocalizedRerootCompoundThroughRule5
          (data.compounds left) (data.compounds right)), ?_, ?_⟩
      · simpa [compoundActualCompareAt] using callbackEq
      · calc
          (localizedOccurrenceRule45ComparisonRecord
            (input.compareLocalizedRerootCompoundThroughRule5
              (data.compounds left) (data.compounds right))).ordering =
              compare (data.keys left) (data.keys right) := data.fullOrdering left right
          _ = compare (rank left) (rank right) := by
            simpa [rank] using keyCompare_rank data left right
    obtain ⟨tracked, sortComputed, permutation, descending⟩ :=
      sortFourLocalizedLigandsTracked_total_of_strictOrdering rank rankInjective callback ranked
    have coherent : orderCoherentOf callback tracked.highestFirst = true := by
      apply (orderCoherentOf_eq_true_iff _ _).mpr
      apply descending.imp
      intro left right lower
      have different : left ≠ right := by
        intro same
        subst right
        omega
      obtain ⟨result, resultEq, ordering⟩ := ranked left right different
      exact ⟨result, resultEq, ordering.trans (Nat.compare_eq_gt.mpr lower)⟩
    have safeComputed : safeTrackedOrderOrderedExecOf callback = some tracked := by
      rw [safeTrackedOrderOrderedExecOf_eq]
      unfold safeTrackedOrderOf
      simp [sortComputed, coherent]
    have count := ContextDescriptorExecutionData.trackedCount_eq_complete
      data injective tracked safeComputed
    have spatialMap : tracked.highestFirst.mapM (fun slot =>
        input.localizedRerootCursorSpatialPoint? (data.frame.cursorAt slot)) =
          some (tracked.highestFirst.map points) := by
      induction tracked.highestFirst with
      | nil => rfl
      | cons slot rest ih =>
        rw [List.mapM_cons, pointAvailable slot, ih]
        rfl
    have safeComputed' : safeTrackedOrderOrderedExecOf
        (input.compareRuleMajorOccurrenceExecAt? target view data.frame) = some tracked := by
      simpa [callback] using safeComputed
    have sortedKeys : tracked.highestFirst.Pairwise
        (fun left right => data.keys right < data.keys left) := by
      exact descending.imp fun h =>
        (keyRank_lt_iff_without_injectivity data.keys _ _).mp h
    have orderEq : tracked.highestFirst = order := by
      apply List.Perm.eq_of_pairwise
        (fun _ _ _ _ h h' => False.elim (lt_asymm h h'))
        sortedKeys orderSorted
      exact permutation.trans orderPerm.symm
    have rationalTracked : RationalTetrahedralDescriptor
        (tracked.highestFirst.map points) raw := by
      simpa [orderEq] using rational
    have rawComputed := (descriptorOfPriorityOrderedPoints?_eq_some_iff _ _).2 rationalTracked
    have evidenceComputed : input.ruleMajorSpatialEvidenceExec? target view =
        some ⟨data.center, data.frame, tracked, tracked.highestFirst.map points⟩ := by
      unfold CertifiedLocalizedCIPInput.ruleMajorSpatialEvidenceExec?
      simp [data.centerComputed, data.frameComputed, safeComputed', spatialMap]
    have execution : input.ruleMajorDescriptorExec? target view = some descriptor := by
      unfold CertifiedLocalizedCIPInput.ruleMajorDescriptorExec?
      simp [evidenceComputed, rawComputed, count, descriptorEq]
    exact execution

/-- Execution returns `none` exactly when no descriptor has an independent complete-root
judgment for any coordinates observed at this actual frame. -/
theorem exec_none_iff_no_completeRootJudgment
    (data : input.ContextDescriptorExecutionData target view) :
    input.ruleMajorDescriptorExec? target view = none ↔
      ¬ ∃ descriptor : LocalizedAuxiliaryLabel, ∃ points : Fin 4 → CartesianPoint3,
        (∀ slot, input.localizedRerootCursorSpatialPoint? (data.frame.cursorAt slot) =
          some (points slot)) ∧
        CompleteRootDescriptorJudgment data.keys points descriptor := by
  constructor
  · intro none
    rintro ⟨descriptor, points, available, judgment⟩
    have someDescriptor := (data.exec_some_iff_completeRootJudgment descriptor).2
      ⟨points, available, judgment⟩
    rw [none] at someDescriptor
    contradiction
  · intro noJudgment
    cases computed : input.ruleMajorDescriptorExec? target view with
    | none => rfl
    | some descriptor =>
      exfalso
      apply noJudgment
      exact ⟨descriptor,
        (data.exec_some_iff_completeRootJudgment descriptor).1 computed⟩

end ContextDescriptorExecutionData

end
end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ContextDescriptorExecutionData
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ContextDescriptorExecutionData.trackedCount_eq_complete
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ContextDescriptorExecutionData.exec_some_iff_completeRootJudgment
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ContextDescriptorExecutionData.exec_none_iff_no_completeRootJudgment
