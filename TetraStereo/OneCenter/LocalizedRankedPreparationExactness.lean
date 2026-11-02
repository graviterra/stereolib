import TetraStereo.OneCenter.LocalizedRankedPreparation

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open Rule6HandednessSemantics RationalTetrahedralPermutation

/-- A descriptor in a genuine priority permutation forces nonzero canonical volume. -/
theorem rationalTetrahedralDescriptor_nonzero_of_permutation
    (point : Fin 4 → CartesianPoint3) (order : List (Fin 4))
    (permutation : order.Perm (List.finRange 4)) (raw : RS)
    (geometry : RationalTetrahedralDescriptor (order.map point) raw) :
    CartesianPoint3.orientedVolume (point 0) (point 1) (point 2) (point 3) ≠ 0 := by
  have positionsPermutation : (order.map Fin.val).Perm (List.range 4) := by
    simpa using permutation.map Fin.val
  let ordering := finFourEquivOfPermutationList (order.map Fin.val) positionsPermutation
  have positionsEq : finFourPermutationList ordering = order.map Fin.val :=
    finFourPermutationList_equivOfPermutationList _ positionsPermutation
  have orderEq : order = [ordering 0, ordering 1, ordering 2, ordering 3] := by
    apply List.map_injective_iff.mpr Fin.val_injective
    change order.map Fin.val = finFourPermutationList ordering
    exact positionsEq.symm
  have pointEq : pointVector (point 0) (point 1) (point 2) (point 3) = point := by
    funext i
    fin_cases i <;> rfl
  intro zero
  have reorderedZero : CartesianPoint3.orientedVolume (point (ordering 0)) (point (ordering 1))
      (point (ordering 2)) (point (ordering 3)) = 0 := by
    have volume := permutedOrientedVolume_eq_if_permutationIsEven
      (point 0) (point 1) (point 2) (point 3) ordering
    simpa [permutedOrientedVolume, pointEq, zero] using volume
  rw [orderEq] at geometry
  rcases geometry with ⟨first, second, third, fourth, points, sign⟩
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at points
  rcases points with ⟨rfl, rfl, rfl, rfl, _⟩
  cases raw <;> simp [reorderedZero] at sign

namespace Bounded

private theorem forall₂_covered {α β : Type} {relation : α → β → Prop} {left : List α} {right : List β}
    (paired : List.Forall₂ relation left right) : ∀ a ∈ left, ∃ b, relation a b := by
  induction paired with
  | nil => simp
  | @cons a b left right head tail ih =>
      intro x present
      rcases List.mem_cons.mp present with rfl | present
      · exact ⟨b, head⟩
      · exact ih x present

/-- Any witnessed finite preparation is recognized by the executable checks. -/
theorem prepareRanked?_total_of_preparation
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel))}
    (callbackFree : input.LocalizedRule3CallbackFreeCarrierCertificate fuel)
    {target : input.LocalizedCIPOccurrence fuel} {view : input.LocalizedDependencyView target}
    (prepared : RankedPreparation input readChildren target view) :
    (prepareRanked? input readChildren callbackFree target view).isSome = true := by
  unfold prepareRanked?
  split
  · rename_i equation
    rw [prepared.centerComputed] at equation
    cases equation
  · rename_i center equation
    have same : center = prepared.center := Option.some.inj (equation.symm.trans prepared.centerComputed)
    subst center
    split
    · rename_i equation
      rw [prepared.baseComputed] at equation
      cases equation
    · rename_i base equation
      have same : base = prepared.base := Option.some.inj (equation.symm.trans prepared.baseComputed)
      subst base
      split
      · rename_i equation
        rw [prepared.frameComputed] at equation
        cases equation
      · rename_i frame equation
        have same : frame = prepared.frame := Option.some.inj (equation.symm.trans prepared.frameComputed)
        subst frame
        split
        · split
          · rename_i equation
            rw [prepared.pointsComputed 0] at equation
            cases equation
          · rename_i p0 equation
            have same : p0 = prepared.point 0 := Option.some.inj (equation.symm.trans (prepared.pointsComputed 0))
            subst p0
            split
            · rename_i equation
              rw [prepared.pointsComputed 1] at equation
              cases equation
            · rename_i p1 equation
              have same : p1 = prepared.point 1 := Option.some.inj (equation.symm.trans (prepared.pointsComputed 1))
              subst p1
              split
              · rename_i equation
                rw [prepared.pointsComputed 2] at equation
                cases equation
              · rename_i p2 equation
                have same : p2 = prepared.point 2 := Option.some.inj (equation.symm.trans (prepared.pointsComputed 2))
                subst p2
                split
                · rename_i equation
                  rw [prepared.pointsComputed 3] at equation
                  cases equation
                · rename_i p3 equation
                  have same : p3 = prepared.point 3 := Option.some.inj (equation.symm.trans (prepared.pointsComputed 3))
                  subst p3
                  split
                  · rfl
                  · rename_i zero
                    exact False.elim (zero prepared.nonzero)
        · rename_i notSeparated
          exact False.elim (notSeparated prepared.separated)

/-- Successful evaluation constructs all finite preparation fields, including canonical
coordinate coverage and nonzero volume; no preselected priority order is needed. -/
theorem preparation_of_descriptor
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel))}
    (callbackFree : input.LocalizedRule3CallbackFreeCarrierCertificate fuel)
    {target : input.LocalizedCIPOccurrence fuel} {view : input.LocalizedDependencyView target}
    {descriptor : LocalizedAuxiliaryLabel}
    (computed : descriptor? input readChildren target view = some descriptor) :
    Nonempty (RankedPreparation input readChildren target view) := by
  unfold descriptor? at computed
  obtain ⟨evidence, evidenceComputed, remainder⟩ := Option.bind_eq_some_iff.mp computed
  obtain ⟨raw, geometryComputed, _⟩ := Option.bind_eq_some_iff.mp remainder
  unfold spatialEvidence? at evidenceComputed
  obtain ⟨center, centerComputed, remainder⟩ := Option.bind_eq_some_iff.mp evidenceComputed
  obtain ⟨base, baseComputed, remainder⟩ := Option.bind_eq_some_iff.mp remainder
  obtain ⟨frame, frameComputed, remainder⟩ := Option.bind_eq_some_iff.mp remainder
  obtain ⟨tracked, trackedComputed, remainder⟩ := Option.bind_eq_some_iff.mp remainder
  obtain ⟨points, pointsComputed, evidenceEq⟩ := Option.bind_eq_some_iff.mp remainder
  have evidenceEq := Option.some.inj evidenceEq
  subst evidence
  have separated : input.FullComparisonSeparated frame :=
    (input.trackedOrder_isSome_iff_separated frame).mp (by simp [trackedComputed])
  obtain ⟨other, otherComputed, permutation, _⟩ := input.trackedOrder_total_of_separated frame separated
  have same : other = tracked := Option.some.inj (otherComputed.symm.trans trackedComputed)
  subst other
  have coverage : ∀ i : Fin 4, ∃ point, input.localizedRerootCursorSpatialPoint? (base.cursorAt i) = some point := by
    intro i
    exact forall₂_covered (TerminalTie.mapM_forall₂ _ _ _ pointsComputed) i
      (permutation.mem_iff.mpr (List.mem_finRange i))
  choose point pointComputed using coverage
  have mapped : tracked.highestFirst.mapM (fun i =>
      input.localizedRerootCursorSpatialPoint? (base.cursorAt i)) = some (tracked.highestFirst.map point) := by
    induction tracked.highestFirst with
    | nil => rfl
    | cons i rest ih =>
        simp only [List.mapM_cons, pointComputed i, ih, List.map_cons]
        rfl
  have pointsEq : points = tracked.highestFirst.map point := Option.some.inj (pointsComputed.symm.trans mapped)
  have geometry : RationalTetrahedralDescriptor (tracked.highestFirst.map point) raw := by
    rw [← pointsEq]
    exact (descriptorOfPriorityOrderedPoints?_eq_some_iff _ raw).mp geometryComputed
  exact ⟨{
    callbackFree, center, centerComputed, base, baseComputed, frame, frameComputed,
    separated, point, pointsComputed := pointComputed,
    nonzero := rationalTetrahedralDescriptor_nonzero_of_permutation point _ permutation raw geometry }⟩

/-- Exact operational success boundary: finite preparation neither loses nor invents a
successful result of the existing bounded descriptor evaluator. -/
theorem prepareRanked?_isSome_iff_descriptor
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel)))
    (callbackFree : input.LocalizedRule3CallbackFreeCarrierCertificate fuel)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    (prepareRanked? input readChildren callbackFree target view).isSome = true ↔
      (descriptor? input readChildren target view).isSome = true := by
  constructor
  · intro successful
    cases prepared : prepareRanked? input readChildren callbackFree target view with
    | none => simp [prepared] at successful
    | some ready => simp [ready.finish_local]
  · intro successful
    cases computed : descriptor? input readChildren target view with
    | none => simp [computed] at successful
    | some descriptor =>
        obtain ⟨prepared⟩ := preparation_of_descriptor callbackFree computed
        exact prepareRanked?_total_of_preparation callbackFree prepared

/-- Preparation and total finishing preserve the complete optional descriptor value. -/
theorem prepareRanked?_map_finish_eq_descriptor
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel)))
    (callbackFree : input.LocalizedRule3CallbackFreeCarrierCertificate fuel)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    (prepareRanked? input readChildren callbackFree target view).map (fun ready => ready.finish.1) =
      descriptor? input readChildren target view := by
  cases prepared : prepareRanked? input readChildren callbackFree target view with
  | none =>
      have notSome : ¬ (descriptor? input readChildren target view).isSome = true := by
        intro successful
        have accepted := (prepareRanked?_isSome_iff_descriptor input readChildren callbackFree target view).mpr successful
        simp [prepared] at accepted
      cases computed : descriptor? input readChildren target view with
      | none => rfl
      | some result => exact False.elim (notSome (by simp [computed]))
  | some ready => simpa using ready.finish_local.symm

end Bounded
end TetraStereo.OneCenter.CertifiedLocalizedCIPInput

namespace TetraStereo.OneCenter.LocalizedShortCircuit
open CertifiedLocalizedCIPInput Certificate.Dependency

/-- The molecular-input prepared entry point preserves every success, refusal and label of
the existing supported constructor. It changes where finite checks occur, not the result domain. -/
theorem certifyPreparedRanked?_map_descriptor_eq_supported (input : Input) (target : Occurrence input) :
    (certifyPreparedRanked? input target).map Sigma.fst =
      (certifySupported? input target).map Sigma.fst := by
  unfold certifyPreparedRanked? prepareSupportedRanked? certifySupported?
  cases checked : input.certified.localizedRule3CallbackFreeCarrierCertificate? (carrierFuel input) with
  | none => simp
  | some callbackFree =>
      simp only [certifyWithSupport?, bind, pure, Option.bind_some,
        Option.map_bind, Function.comp_def, Option.map_some,
        SupportedRankedPreparation.finish]
      let cache := Cached.buildRuntimeCache input
      let support := Linear.produceDependencySupport input cache callbackFree target
      have equality := Bounded.prepareRanked?_map_finish_eq_descriptor input.certified
        (input.certified.localizedRerootChildrenFromCarrier? cache.carrier) callbackFree target
        (input.certified.localizedDependencyView (lookup support.facts) target)
      rw [← Bounded.descriptorCertificate?_map_descriptor input.certified _ callbackFree] at equality
      simpa only [Option.map_eq_bind, Function.comp_def] using equality

end TetraStereo.OneCenter.LocalizedShortCircuit
