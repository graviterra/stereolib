import TetraStereo.OneCenter.LocalizedRerootRule5Relabel
import TetraStereo.OneCenter.LocalizedRuleMajorCumulativeOrder
import TetraStereo.OneCenter.LocalizedRuleMajorCumulativeBuilder
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! # Rule-5 relabeling for the whole-rule cumulative builder

The Rule-5 observation at each node is a function of its Rule-4a and Rule-4b observations.
Consequently, adding Rule-5 preserves the comparison of the first three whole-hierarchy columns.
If those three columns tie, the three-component shape reconstructs every Rule-4c vector, so the
added column also ties. This is the sorting fact needed by the actual whole-rule builder.
-/

namespace TetraStereo.OneCenter
open CertifiedLocalizedCIPInput

namespace CertifiedLocalizedCIPInput

open OfficialRuleMajorKey
open CompilerProjectionFidelity

variable (input : CertifiedLocalizedCIPInput)
variable {carrierFuel : Nat}

private theorem compareNat_sound_local (left right : Nat)
    (h : compareNat left right = Ordering.eq) : left = right :=
  (compareNat_eq_eq_iff left right).1 h

private theorem sparseNatTables_compare_eq_iff
    (left right : List (List (OfficialSparseEntry Nat))) :
    compareSparseLayers compareNat left right = Ordering.eq ↔ left = right :=
  compareSparseLayers_eq_eq_iff compareNat compareNat_self compareNat_sound_local left right

private theorem compareRuleMajorCumulativeColumnTables_eq_iff (width : Nat)
    (left right : input.LocalizedRerootCumulativeRule45Key) :
    input.compareRuleMajorCumulativeColumnTables width left right = Ordering.eq ↔
      input.ruleMajorCumulativeColumns width left = input.ruleMajorCumulativeColumns width right := by
  unfold compareRuleMajorCumulativeColumnTables
  exact list_compareLex_eq_eq_iff
    (compareSparseLayers compareNat)
    (fun table => compareSparseLayers_self compareNat compareNat_self table)
    (fun first second => sparseNatTables_compare_eq_iff first second |>.1)
    (input.ruleMajorCumulativeColumns width left)
    (input.ruleMajorCumulativeColumns width right)

private theorem projectRule5LiftKey_column (same : Bool)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (shaped : input.Stage4cShaped key) (index : Nat) (beforeRule5 : index < 3) :
    projectCumulative index (input.rule5LiftKey same key).descriptor =
      projectCumulative index key.descriptor := by
  have getD_before_append {values : List Nat} (added : Nat) (fallback : Nat)
      (bound : index < values.length) :
      (values ++ [added]).getD index fallback = values.getD index fallback := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left bound]
  unfold projectCumulative
  change
    ((key.descriptor.map (rule5LiftLayer same)).map
      (List.map fun entry => (entry.1, entry.2.getD index 0))) =
      key.descriptor.map (List.map fun entry => (entry.1, entry.2.getD index 0))
  rw [List.map_map]
  apply List.map_congr_left
  intro layer hlayer
  change (rule5LiftLayer same layer).map
      (fun entry => (entry.1, entry.2.getD index 0)) =
    layer.map (fun entry => (entry.1, entry.2.getD index 0))
  unfold rule5LiftLayer
  rw [List.map_map]
  apply List.map_congr_left
  intro entry hentry
  simp only [Function.comp_apply]
  have observation :
      (entry.2 ++ [rule5Bit same entry.2]).getD index 0 =
        entry.2.getD index 0 := by
    exact getD_before_append (rule5Bit same entry.2) 0 (by
      have entryShaped := shaped layer hlayer entry hentry
      omega)
  simpa [rule5Lift] using congrArg (fun value : Nat => (entry.1, value)) observation

private theorem ruleMajorColumns3_rule5LiftKey (same : Bool)
    (key : input.LocalizedRerootCumulativeRule45Key) (shaped : input.Stage4cShaped key) :
    input.ruleMajorCumulativeColumns 3 (input.rule5LiftKey same key) =
      input.ruleMajorCumulativeColumns 3 key := by
  unfold ruleMajorCumulativeColumns
  apply List.map_congr_left
  intro index hindex
  have indexLt : index < 3 := List.mem_range.mp hindex
  exact projectRule5LiftKey_column input same key shaped index indexLt

private theorem compareRuleMajorCumulativeDescriptor_rule5LiftKey_prefix (same : Bool)
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (leftShaped : input.Stage4cShaped left) (rightShaped : input.Stage4cShaped right) :
    input.compareRuleMajorCumulativeDescriptor 3
        (input.rule5LiftKey same left) (input.rule5LiftKey same right) =
      input.compareRuleMajorCumulativeDescriptor 3 left right := by
  have leftColumns := ruleMajorColumns3_rule5LiftKey input same left leftShaped
  have rightColumns := ruleMajorColumns3_rule5LiftKey input same right rightShaped
  have columnsCompare :
      input.compareRuleMajorCumulativeColumnTables 3
          (input.rule5LiftKey same left) (input.rule5LiftKey same right) =
        input.compareRuleMajorCumulativeColumnTables 3 left right := by
    unfold compareRuleMajorCumulativeColumnTables
    rw [leftColumns, rightColumns]
  rw [input.compareRuleMajorCumulativeDescriptor_eq_lexColumnsFunction]
  simp only [compareLex, Ordering.byKey]
  rw [columnsCompare]
  rfl

private theorem descriptor_eq_of_projected_columns_eq
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (leftShaped : input.Stage4cShaped left) (rightShaped : input.Stage4cShaped right)
    (columnsEqual : input.ruleMajorCumulativeColumns 3 left =
      input.ruleMajorCumulativeColumns 3 right) :
    left.descriptor = right.descriptor := by
  have components :
      projectCumulative 0 left.descriptor = projectCumulative 0 right.descriptor ∧
      projectCumulative 1 left.descriptor = projectCumulative 1 right.descriptor ∧
      projectCumulative 2 left.descriptor = projectCumulative 2 right.descriptor := by
    change [projectCumulative 0 left.descriptor, projectCumulative 1 left.descriptor,
        projectCumulative 2 left.descriptor] =
      [projectCumulative 0 right.descriptor, projectCumulative 1 right.descriptor,
        projectCumulative 2 right.descriptor] at columnsEqual
    have first := List.cons.inj columnsEqual
    have second := List.cons.inj first.2
    have third := List.cons.inj second.2
    exact ⟨first.1, second.1, third.1⟩
  rcases components with ⟨hzero, hone, htwo⟩
  have entryValues_eq {a b : OfficialSparseEntry (List Nat)}
      (ha : a.2.length = 3) (hb : b.2.length = 3)
      (h0 : a.1 = b.1) (h1 : a.2.getD 0 0 = b.2.getD 0 0)
      (h2 : a.2.getD 1 0 = b.2.getD 1 0)
      (h3 : a.2.getD 2 0 = b.2.getD 2 0) : a = b := by
    have reconstruct (values : List Nat) (shape : values.length = 3) :
        values = [values.getD 0 0, values.getD 1 0, values.getD 2 0] := by
      cases values with
      | nil => simp at shape
      | cons first tail =>
          cases tail with
          | nil => simp at shape
          | cons second tail =>
              cases tail with
              | nil => simp at shape
              | cons third tail =>
                  cases tail with
                  | nil => simp [List.getD]
                  | cons extra rest => simp at shape
    rcases a with ⟨pathA, valuesA⟩
    rcases b with ⟨pathB, valuesB⟩
    simp only [Prod.mk.injEq]
    refine ⟨h0, ?_⟩
    rw [reconstruct valuesA ha, reconstruct valuesB hb, h1, h2, h3]

  have layer_eq_of_projection_eq
      (a b : List (OfficialSparseEntry (List Nat)))
      (ha : ∀ entry ∈ a, entry.2.length = 3)
      (hb : ∀ entry ∈ b, entry.2.length = 3)
      (p0 : a.map (fun entry => (entry.1, entry.2.getD 0 0)) =
        b.map (fun entry => (entry.1, entry.2.getD 0 0)))
      (p1 : a.map (fun entry => (entry.1, entry.2.getD 1 0)) =
        b.map (fun entry => (entry.1, entry.2.getD 1 0)))
      (p2 : a.map (fun entry => (entry.1, entry.2.getD 2 0)) =
        b.map (fun entry => (entry.1, entry.2.getD 2 0))) : a = b := by
    induction a generalizing b with
    | nil =>
        cases b with
        | nil => rfl
        | cons entry tail => simp at p0
    | cons entry tail ih =>
        cases b with
        | nil => simp at p0
        | cons other rest =>
            simp only [List.map_cons, List.cons.injEq] at p0 p1 p2
            rcases Prod.mk.inj p0.1 with ⟨addressEq, value0Eq⟩
            rcases Prod.mk.inj p1.1 with ⟨_, value1Eq⟩
            rcases Prod.mk.inj p2.1 with ⟨_, value2Eq⟩
            have headEq := entryValues_eq (ha entry List.mem_cons_self)
              (hb other List.mem_cons_self) addressEq value0Eq value1Eq value2Eq
            have tailEq := ih rest
              (fun value member => ha value (List.mem_cons_of_mem entry member))
              (fun value member => hb value (List.mem_cons_of_mem other member))
              p0.2 p1.2 p2.2
            rw [headEq, tailEq]

  have descriptor_eq_of_columns
      (a b : List (List (OfficialSparseEntry (List Nat))))
      (ha : ∀ layer ∈ a, ∀ entry ∈ layer, entry.2.length = 3)
      (hb : ∀ layer ∈ b, ∀ entry ∈ layer, entry.2.length = 3)
      (p0 : projectCumulative 0 a = projectCumulative 0 b)
      (p1 : projectCumulative 1 a = projectCumulative 1 b)
      (p2 : projectCumulative 2 a = projectCumulative 2 b) : a = b := by
    induction a generalizing b with
    | nil =>
        cases b with
        | nil => rfl
        | cons layer tail => simp [projectCumulative] at p0
    | cons layer tail ih =>
        cases b with
        | nil => simp [projectCumulative] at p0
        | cons other rest =>
            simp only [projectCumulative, List.map_cons, List.cons.injEq] at p0 p1 p2
            have headEq := layer_eq_of_projection_eq layer other
              (fun entry member => ha layer List.mem_cons_self entry member)
              (fun entry member => hb other List.mem_cons_self entry member)
              p0.1 p1.1 p2.1
            have tailEq := ih rest
              (fun value member entry entryMem =>
                ha value (List.mem_cons_of_mem layer member) entry entryMem)
              (fun value member entry entryMem =>
                hb value (List.mem_cons_of_mem other member) entry entryMem)
              p0.2 p1.2 p2.2
            simp [headEq, tailEq]
  exact descriptor_eq_of_columns left.descriptor right.descriptor leftShaped rightShaped
    hzero hone htwo

private theorem compareRuleMajorCumulativeDescriptor_parts_eq
    (width : Nat) (left right : input.LocalizedRerootCumulativeRule45Key)
    (comparison : input.compareRuleMajorCumulativeDescriptor width left right = Ordering.eq) :
    OfficialRuleMajorKey.compare left.constitutional right.constitutional = Ordering.eq ∧
      input.compareRuleMajorCumulativeColumnTables width left right = Ordering.eq := by
  rw [input.compareRuleMajorCumulativeDescriptor_eq_lexColumns] at comparison
  simp only [compareLex, Ordering.byKey] at comparison
  cases hconst : OfficialRuleMajorKey.compare left.constitutional right.constitutional with
  | lt => simp [hconst] at comparison
  | gt => simp [hconst] at comparison
  | eq =>
      have hcolumns : input.compareRuleMajorCumulativeColumnTables width left right = Ordering.eq := by
        simpa [hconst, Ordering.then] using comparison
      exact ⟨rfl, hcolumns⟩

private theorem compareRuleMajorCumulativeDescriptor_rule5LiftKey (same : Bool)
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (leftShaped : input.Stage4cShaped left) (rightShaped : input.Stage4cShaped right) :
    input.compareRuleMajorCumulativeDescriptor 4
        (input.rule5LiftKey same left) (input.rule5LiftKey same right) =
      input.compareRuleMajorCumulativeDescriptor 3 left right := by
  rcases baseCmp : input.compareRuleMajorCumulativeDescriptor 3 left right with _ | _ | _
  · have liftedCmp : input.compareRuleMajorCumulativeDescriptor 3
        (input.rule5LiftKey same left) (input.rule5LiftKey same right) = Ordering.lt := by
      rw [compareRuleMajorCumulativeDescriptor_rule5LiftKey_prefix input same left right
        leftShaped rightShaped, baseCmp]
    have stage4 := input.compareRuleMajorCumulativeDescriptor_prefix_preserves 3 1
      (input.rule5LiftKey same left) (input.rule5LiftKey same right) liftedCmp
    simpa [ruleMajorStageWidth] using stage4
  · have liftedCmp : input.compareRuleMajorCumulativeDescriptor 3
        (input.rule5LiftKey same left) (input.rule5LiftKey same right) = Ordering.eq := by
      rw [compareRuleMajorCumulativeDescriptor_rule5LiftKey_prefix input same left right
        leftShaped rightShaped, baseCmp]
    obtain ⟨hconst, hcolumns⟩ :=
      compareRuleMajorCumulativeDescriptor_parts_eq input 3 left right baseCmp
    have columnsEqual :=
      (compareRuleMajorCumulativeColumnTables_eq_iff input 3 left right).1 hcolumns
    have descriptorEqual := descriptor_eq_of_projected_columns_eq input left right leftShaped
      rightShaped columnsEqual
    have liftedDescriptorEqual : (input.rule5LiftKey same left).descriptor =
        (input.rule5LiftKey same right).descriptor := by
      simp only [rule5LiftKey]
      rw [descriptorEqual]
    have liftedColumnsEqual :
        input.ruleMajorCumulativeColumns 4 (input.rule5LiftKey same left) =
          input.ruleMajorCumulativeColumns 4 (input.rule5LiftKey same right) := by
      simp [ruleMajorCumulativeColumns, liftedDescriptorEqual]
    have liftedColumnsCmp :
        input.compareRuleMajorCumulativeColumnTables 4
          (input.rule5LiftKey same left) (input.rule5LiftKey same right) = Ordering.eq :=
      (compareRuleMajorCumulativeColumnTables_eq_iff input 4
        (input.rule5LiftKey same left) (input.rule5LiftKey same right)).2 liftedColumnsEqual
    have hconstLift : OfficialRuleMajorKey.compare
        (input.rule5LiftKey same left).constitutional
        (input.rule5LiftKey same right).constitutional = Ordering.eq := by
      simpa [rule5LiftKey] using hconst
    rw [input.compareRuleMajorCumulativeDescriptor_eq_lexColumns]
    simp only [compareLex, Ordering.byKey]
    rw [hconstLift, liftedColumnsCmp]
    rfl
  · have liftedCmp : input.compareRuleMajorCumulativeDescriptor 3
        (input.rule5LiftKey same left) (input.rule5LiftKey same right) = Ordering.gt := by
      rw [compareRuleMajorCumulativeDescriptor_rule5LiftKey_prefix input same left right
        leftShaped rightShaped, baseCmp]
    have stage4 := input.compareRuleMajorCumulativeDescriptor_prefix_preserves_gt 3 1
      (input.rule5LiftKey same left) (input.rule5LiftKey same right) liftedCmp
    simpa [ruleMajorStageWidth] using stage4

private theorem insertRuleMajorRule5LiftKey (same : Bool)
    (key : input.LocalizedRerootCumulativeRule45Key) (keyShaped : input.Stage4cShaped key) :
    ∀ keys : List input.LocalizedRerootCumulativeRule45Key,
      (∀ item ∈ keys, input.Stage4cShaped item) →
      insertKeyBy (input.compareRuleMajorCumulativeDescriptor 4)
          (input.rule5LiftKey same key) (keys.map (input.rule5LiftKey same)) =
        (insertKeyBy (input.compareRuleMajorCumulativeDescriptor 3) key keys).map
          (input.rule5LiftKey same)
  | [], _ => rfl
  | head :: tail, shaped => by
      have comparison := compareRuleMajorCumulativeDescriptor_rule5LiftKey input same key head
        keyShaped (shaped head List.mem_cons_self)
      simp only [List.map_cons, insertKeyBy, comparison]
      cases input.compareRuleMajorCumulativeDescriptor 3 key head <;>
        simp [insertRuleMajorRule5LiftKey same key keyShaped tail
          (fun item member => shaped item (List.mem_cons_of_mem head member))]

private theorem sortRuleMajorRule5LiftKey (same : Bool) :
    ∀ keys : List input.LocalizedRerootCumulativeRule45Key,
      (∀ item ∈ keys, input.Stage4cShaped item) →
      sortKeysBy (input.compareRuleMajorCumulativeDescriptor 4)
          (keys.map (input.rule5LiftKey same)) =
        (sortKeysBy (input.compareRuleMajorCumulativeDescriptor 3) keys).map
          (input.rule5LiftKey same)
  | [], _ => rfl
  | key :: tail, shaped => by
      have tailShaped : ∀ item ∈ tail, input.Stage4cShaped item :=
        fun item member => shaped item (List.mem_cons_of_mem key member)
      have sortedTailShaped : ∀ item ∈
          sortKeysBy (input.compareRuleMajorCumulativeDescriptor 3) tail,
          input.Stage4cShaped item := fun item member =>
        tailShaped item
          ((input.sortKeysBy_ruleMajorCumulative_perm 3 tail).mem_iff.1 member)
      simp only [List.map_cons, sortKeysBy]
      rw [sortRuleMajorRule5LiftKey same tail tailShaped,
        insertRuleMajorRule5LiftKey input same key (shaped key List.mem_cons_self)
          (sortKeysBy (input.compareRuleMajorCumulativeDescriptor 3) tail) sortedTailShaped]

theorem sortRuleMajorCumulativeKeys_rule5LiftKey (same : Bool)
    (rule4bReference rule5Reference : RS)
    (keys : List input.LocalizedRerootCumulativeRule45Key)
    (shaped : ∀ item ∈ keys, input.Stage4cShaped item) :
    input.sortRuleMajorCumulativeKeys (.rule5 rule4bReference rule5Reference)
        (keys.map (input.rule5LiftKey same)) =
      (input.sortRuleMajorCumulativeKeys (.rule4c rule4bReference) keys).map
        (input.rule5LiftKey same) := by
  change sortKeysBy (input.compareRuleMajorCumulativeDescriptor 4)
      (keys.map (input.rule5LiftKey same)) = _
  change _ = (sortKeysBy (input.compareRuleMajorCumulativeDescriptor 3) keys).map
    (input.rule5LiftKey same)
  exact sortRuleMajorRule5LiftKey input same keys shaped

private theorem mapM_map_option {α β γ : Type*} (f : α → Option β) (g : α → Option γ)
    (h : β → γ) :
    ∀ l : List α, (∀ a ∈ l, g a = (f a).map h) →
      l.mapM g = (l.mapM f).map (List.map h)
  | [], _ => rfl
  | a :: l, agree => by
      rw [List.mapM_cons, List.mapM_cons, agree a List.mem_cons_self,
        mapM_map_option f g h l fun x hx => agree x (List.mem_cons_of_mem a hx)]
      cases f a <;> cases l.mapM f <;> rfl

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

theorem buildRuleMajorCumulativeWithRead?_rule4c_shaped
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} (reference : RS)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.buildRuleMajorCumulativeWithRead? (.rule4c reference) read fuel cursor =
        some key → input.Stage4cShaped key
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
            exact priority_rule4c_length reference _
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
            exact priority_rule4c_length reference _
          · cases hkeys : children.mapM
                (input.buildRuleMajorCumulativeWithRead? (.rule4c reference) read fuel) with
            | none => simp [hkeys] at h
            | some childKeys =>
                simp only [hkeys, Option.bind_some, Option.some.injEq] at h
                subst h
                have childShaped : ∀ child ∈ childKeys, input.Stage4cShaped child :=
                  fun child member => by
                    obtain ⟨cursor', _, built⟩ :=
                      mem_of_mapM_some _ children childKeys hkeys child member
                    exact buildRuleMajorCumulativeWithRead?_rule4c_shaped input reference read
                      fuel cursor' child built
                have sortedPerm :
                    input.sortRuleMajorCumulativeKeys (.rule4c reference) childKeys |>.Perm
                      childKeys := by
                  simpa [sortRuleMajorCumulativeKeys, ruleMajorStageWidth] using
                    input.sortKeysBy_ruleMajorCumulative_perm 3 childKeys
                have sortedShaped : ∀ child ∈
                    input.sortRuleMajorCumulativeKeys (.rule4c reference) childKeys,
                    input.Stage4cShaped child := fun child member =>
                  childShaped child (sortedPerm.mem_iff.1 member)
                intro layer hlayer entry hentry
                simp only [List.cons_append, List.nil_append, List.mem_cons] at hlayer
                rcases hlayer with rfl | hlayer
                · simp only [List.mem_singleton] at hentry
                  subst hentry
                  exact priority_rule4c_length reference _
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

theorem buildRuleMajorCumulativeWithRead?_rule5
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (rule4bReference rule5Reference : RS)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    ∀ fuel (cursor : input.LocalizedRerootCursor carrierFuel),
      input.buildRuleMajorCumulativeWithRead? (.rule5 rule4bReference rule5Reference)
          read fuel cursor =
        (input.buildRuleMajorCumulativeWithRead? (.rule4c rule4bReference) read fuel cursor).map
          (input.rule5LiftKey (rule5Reference == rule4bReference))
  | 0, cursor => by
      unfold buildRuleMajorCumulativeWithRead?
      cases hch : input.localizedRerootChildren? cursor with
      | none => rfl
      | some children =>
          simp only [Option.bind_eq_bind, Option.bind_some]
          split
          · simp only [Option.map_some, localizedCumulativeRule45TerminalKey,
              rule5LiftKey, List.map_cons, List.map_nil, rule5LiftLayer,
              rule5Lift_priority]
          · rfl
  | fuel + 1, cursor => by
      have ih := buildRuleMajorCumulativeWithRead?_rule5 input rule4bReference
        rule5Reference read fuel
      unfold buildRuleMajorCumulativeWithRead?
      cases hch : input.localizedRerootChildren? cursor with
      | none => rfl
      | some children =>
          simp only [Option.bind_eq_bind, Option.bind_some]
          split
          · simp only [Option.map_some, localizedCumulativeRule45TerminalKey,
              rule5LiftKey, List.map_cons, List.map_nil, rule5LiftLayer,
              rule5Lift_priority]
          · rw [mapM_map_option _ _ _ children fun child _ => ih child]
            cases hkeys : children.mapM
                (input.buildRuleMajorCumulativeWithRead? (.rule4c rule4bReference) read fuel) with
            | none => rfl
            | some childKeys =>
                have childShaped : ∀ key ∈ childKeys, input.Stage4cShaped key :=
                  fun key member => by
                    obtain ⟨child, _, built⟩ :=
                      mem_of_mapM_some _ children childKeys hkeys key member
                    exact input.buildRuleMajorCumulativeWithRead?_rule4c_shaped
                      rule4bReference read fuel child key built
                have sortedPerm :
                    input.sortRuleMajorCumulativeKeys (.rule4c rule4bReference) childKeys |>.Perm
                      childKeys := by
                  simpa [sortRuleMajorCumulativeKeys, ruleMajorStageWidth] using
                    input.sortKeysBy_ruleMajorCumulative_perm 3 childKeys
                have sortedShaped : ∀ key ∈
                    input.sortRuleMajorCumulativeKeys (.rule4c rule4bReference) childKeys,
                    input.Stage4cShaped key := fun key member =>
                  childShaped key (sortedPerm.mem_iff.1 member)
                simp only [Option.map_some, Option.bind_some, Option.some.injEq]
                rw [sortRuleMajorCumulativeKeys_rule5LiftKey input
                    (rule5Reference == rule4bReference) rule4bReference rule5Reference
                    childKeys childShaped]
                simp only [localizedCumulativeRule45StepKey]
                rw [input.mergeDescriptor_rule5LiftKey,
                  input.mergeLabel_rule5LiftKey,
                  input.mergeRankedLabel_rule5LiftKey _ _ sortedShaped]
                simp only [rule5LiftKey,
                  List.map_map, List.map_append, List.map_cons, List.map_nil,
                  rule5LiftLayer, rule5Lift_priority]
                rfl

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.sortRuleMajorCumulativeKeys_rule5LiftKey
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithRead?_rule4c_shaped
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithRead?_rule5
