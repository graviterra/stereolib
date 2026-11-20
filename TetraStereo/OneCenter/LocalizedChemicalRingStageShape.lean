import TetraStereo.OneCenter.LocalizedChemicalRingStageObservable
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! Every actual current rule-major build has the fixed descriptor width of its stage.
This supplies the shape condition in comparison-visible sorting invariance. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingStageShape
open CertifiedLocalizedCIPInput LocalizedChemicalRingStageObservable
open OfficialRuleMajorKey

theorem priority_length (stage : LocalizedCumulativeRule45Stage)
    (label : Option LocalizedAuxiliaryLabel) :
    (localizedCumulativeRule45Priority stage label).length = ruleMajorStageWidth stage := by
  cases stage <;> rfl

theorem stageWidth_positive (stage : LocalizedCumulativeRule45Stage) : 0 < ruleMajorStageWidth stage := by
  cases stage <;> simp [ruleMajorStageWidth, localizedCumulativeRule45Priority]

private theorem mem_of_mapM_some {α β : Type*} (f : α → Option β) :
    ∀ (l : List α) (ys : List β), l.mapM f = some ys →
      ∀ y ∈ ys, ∃ a ∈ l, f a = some y
  | [], ys, h, y, hy => by
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst h
      simp at hy
  | a :: l, ys, h, y, hy => by
      rw [List.mapM_cons] at h
      cases hfa : f a with
      | none => simp [hfa] at h
      | some b =>
          cases hl : l.mapM f with
          | none => simp [hfa, hl] at h
          | some bs =>
              simp only [hfa, hl, Option.bind_eq_bind, Option.bind_some,
                Option.pure_def, Option.some.injEq] at h
              subst h
              rcases List.mem_cons.1 hy with rfl | hy'
              · exact ⟨a, List.mem_cons_self, hfa⟩
              · obtain ⟨a', ha', hfa'⟩ := mem_of_mapM_some f l bs hl y hy'
                exact ⟨a', List.mem_cons_of_mem a ha', hfa'⟩

private theorem fst_mem_of_mem_zipIdx {α : Type*} (x : α × Nat) :
    ∀ (l : List α) (n : Nat), x ∈ l.zipIdx n → x.1 ∈ l
  | [], _, h => by simp at h
  | a :: l, n, h => by
      rw [List.zipIdx_cons] at h
      rcases List.mem_cons.1 h with rfl | h'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem a (fst_mem_of_mem_zipIdx x l (n + 1) h')

private theorem mem_getD_nil {α : Type*} (layers : List (List α))
    (index : Nat) (entry : α) (member : entry ∈ layers.getD index []) :
    ∃ layer ∈ layers, entry ∈ layer := by
  rw [List.getD_eq_getElem?_getD] at member
  cases h : layers[index]? with
  | none => rw [h] at member; simp at member
  | some layer =>
      rw [h] at member
      exact ⟨layer, List.mem_of_getElem? h, member⟩

theorem build_shaped
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.buildRuleMajorCumulativeWithRead? stage read fuel cursor =
        some key → Shaped (ruleMajorStageWidth stage) key.descriptor
  | 0, cursor, key, h => by
      unfold buildRuleMajorCumulativeWithRead? at h
      cases hch : input.localizedRerootChildren? cursor with
      | none => simp [hch] at h
      | some children =>
          simp only [hch, Option.bind_eq_bind, Option.bind_some] at h
          split at h
          · cases h
            intro layer hlayer entry hentry
            simp only [List.mem_singleton] at hlayer
            subst hlayer
            simp only [List.mem_singleton] at hentry
            subst hentry
            exact priority_length stage _
          · cases h
  | fuel + 1, cursor, key, h => by
      unfold buildRuleMajorCumulativeWithRead? at h
      cases hch : input.localizedRerootChildren? cursor with
      | none => simp [hch] at h
      | some children =>
          simp only [hch, Option.bind_eq_bind, Option.bind_some] at h
          split at h
          · cases h
            intro layer hlayer entry hentry
            simp only [List.mem_singleton] at hlayer
            subst hlayer
            simp only [List.mem_singleton] at hentry
            subst hentry
            exact priority_length stage _
          · cases hkeys : children.mapM
                (input.buildRuleMajorCumulativeWithRead? stage read fuel) with
            | none => simp [hkeys] at h
            | some childKeys =>
                simp only [hkeys, Option.bind_some, Option.some.injEq] at h
                subst h
                have childShaped : ∀ child ∈ childKeys, Shaped (ruleMajorStageWidth stage) child.descriptor :=
                  fun child member => by
                    obtain ⟨cursor', _, built⟩ :=
                      mem_of_mapM_some _ children childKeys hkeys child member
                    exact build_shaped input stage read
                      fuel cursor' child built
                have sortedPerm :
                    input.sortRuleMajorCumulativeKeys stage childKeys |>.Perm
                      childKeys := by
                  simpa [sortRuleMajorCumulativeKeys, ruleMajorStageWidth] using
                    input.sortKeysBy_ruleMajorCumulative_perm (ruleMajorStageWidth stage) childKeys
                have sortedShaped : ∀ child ∈
                    input.sortRuleMajorCumulativeKeys stage childKeys,
                    Shaped (ruleMajorStageWidth stage) child.descriptor := fun child member =>
                  childShaped child (sortedPerm.mem_iff.1 member)
                intro layer hlayer entry hentry
                simp only [List.cons_append, List.nil_append, List.mem_cons] at hlayer
                rcases hlayer with rfl | hlayer
                · simp only [List.mem_singleton] at hentry
                  subst hentry
                  exact priority_length stage _
                · unfold mergeLocalizedRerootDescriptorChildren at hlayer
                  simp only [List.mem_map, List.mem_range] at hlayer
                  obtain ⟨depth, _, rfl⟩ := hlayer
                  rw [List.mem_flatMap] at hentry
                  obtain ⟨child, hchild, hentry⟩ := hentry
                  unfold prefixLayer at hentry
                  rw [List.mem_map] at hentry
                  obtain ⟨entry', hentry', rfl⟩ := hentry
                  obtain ⟨layer', hlayer', hmem⟩ := mem_getD_nil _ depth entry' hentry'
                  exact sortedShaped child.1 (fst_mem_of_mem_zipIdx child _ 0 hchild)
                    layer' hlayer' entry' hmem


end TetraStereo.OneCenter.LocalizedChemicalRingStageShape

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStageShape.build_shaped
