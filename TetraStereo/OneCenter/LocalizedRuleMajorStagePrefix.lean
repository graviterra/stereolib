import TetraStereo.OneCenter.LocalizedRuleMajorCumulativeBuilder
import TetraStereo.OneCenter.LocalizedRuleMajorCumulativeOrder
import TetraStereo.OneCenter.OfficialRuleMajorCompilerProjectionFidelity
import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableOrder
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The prefix projection retains constitutional comparison data and the first `width` complete
rule-major descriptor columns. -/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

variable {V : Type*}

structure RuleMajorPrefixObservable (V : Type*) where
  rule1a : List (List (OfficialSparseEntry Nat))
  rule1b : List (List (OfficialSparseEntry Nat))
  rule2 : List (List (OfficialSparseEntry Nat))
  columns : List (List (List (OfficialSparseEntry Nat)))
  deriving DecidableEq

def ruleMajorPrefixObservable (input : CertifiedLocalizedCIPInput) (width : Nat)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    RuleMajorPrefixObservable input.Atom where
  rule1a := key.constitutional.rule1a
  rule1b := key.constitutional.rule1b
  rule2 := key.constitutional.rule2
  columns := input.ruleMajorCumulativeColumns width key

def compareRuleMajorPrefixObservable : RuleMajorPrefixObservable V →
    RuleMajorPrefixObservable V → Ordering := fun left right =>
  compareLex
    (Ordering.byKey RuleMajorPrefixObservable.rule1a
      (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat))
    (compareLex
      (Ordering.byKey RuleMajorPrefixObservable.rule1b
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b))
      (compareLex
        (Ordering.byKey RuleMajorPrefixObservable.rule2
          (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat))
        (Ordering.byKey RuleMajorPrefixObservable.columns
          (List.compareLex (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat)))))
    left right

private theorem prefixListCompare_eq_iff {α : Type*} (cmp : α → α → Ordering)
    (cmpEq : ∀ a b, cmp a b = Ordering.eq ↔ a = b) :
    ∀ left right : List α, List.compareLex cmp left right = Ordering.eq ↔ left = right := by
  intro left
  induction left with
  | nil => intro right; exact List.compareLex_nil_left_eq_eq.trans eq_comm
  | cons head tail ih =>
      intro right
      cases right with
      | nil => exact List.compareLex_nil_right_eq_eq
      | cons otherHead otherTail =>
          rw [List.compareLex_cons_cons, Ordering.then_eq_eq]
          constructor
          · rintro ⟨headEq, tailEq⟩
            rw [(cmpEq head otherHead).mp headEq, (ih otherTail).mp tailEq]
          · intro equal
            injection equal with headEq tailEq
            exact ⟨(cmpEq head otherHead).mpr headEq, (ih otherTail).mpr tailEq⟩

private theorem prefixOrderingThenAssoc (a b c : Ordering) :
    (a.then b).then c = a.then (b.then c) := by
  cases a <;> cases b <;> rfl

private theorem prefixOrderingFourAssoc (a b c d : Ordering) :
    a.then (b.then (c.then d)) = (a.then (b.then c)).then d := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem compareRuleMajorPrefixObservable_eq_iff (left right : RuleMajorPrefixObservable V) :
    compareRuleMajorPrefixObservable left right = Ordering.eq ↔ left = right := by
  cases left with
  | mk l1a l1b l2 ld =>
    cases right with
    | mk r1a r1b r2 rd =>
      simp [compareRuleMajorPrefixObservable, compareLex_eq_eq, Ordering.byKey,
        compareSparseLayers_compareNat_eq_iff,
        compareSparseLayers_compareRule1b_eq_iff,
        prefixListCompare_eq_iff
          (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat)
          compareSparseLayers_compareNat_eq_iff]

theorem compareRuleMajorPrefixObservable_transCmp :
    Std.TransCmp (@compareRuleMajorPrefixObservable V) := by
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  haveI : Std.TransCmp OfficialRuleMajorKey.compareRule1b := by
    unfold OfficialRuleMajorKey.compareRule1b
    infer_instance
  unfold compareRuleMajorPrefixObservable
    OfficialRuleMajorKey.compareSparseLayers
    OfficialRuleMajorKey.compareSparseLayer
    OfficialRuleMajorKey.compareSparseEntry
  infer_instance

theorem compareRuleMajorPrefixObservable_orientedCmp :
    Std.OrientedCmp (@compareRuleMajorPrefixObservable V) := by
  letI : Std.OrientedCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  haveI : Std.OrientedCmp OfficialRuleMajorKey.compareRule1b := by
    unfold OfficialRuleMajorKey.compareRule1b
    infer_instance
  unfold compareRuleMajorPrefixObservable
    OfficialRuleMajorKey.compareSparseLayers
    OfficialRuleMajorKey.compareSparseLayer
    OfficialRuleMajorKey.compareSparseEntry
  infer_instance

theorem compareRuleMajorPrefixObservable_key_eq
    (input : CertifiedLocalizedCIPInput) (width : Nat)
    (left right : input.LocalizedRerootCumulativeRule45Key) :
    compareRuleMajorPrefixObservable
      (input.ruleMajorPrefixObservable width left)
      (input.ruleMajorPrefixObservable width right) =
      input.compareRuleMajorCumulativeDescriptor width left right := by
  rw [input.compareRuleMajorCumulativeDescriptor_eq_lexColumns]
  simp only [compareRuleMajorPrefixObservable, ruleMajorPrefixObservable,
    compareLex, Ordering.byKey, OfficialRuleMajorKey.compare,
    compareRuleMajorCumulativeColumnTables, ruleMajorCumulativeColumns]
  exact prefixOrderingFourAssoc _ _ _ _

theorem ruleMajorPrefixObservable_pairwise_of_descending
    (input : CertifiedLocalizedCIPInput) {width totalWidth : Nat}
    (extra : Nat) (widthPlus : totalWidth = width + extra)
    (keys : List input.LocalizedRerootCumulativeRule45Key)
    (descending : input.RuleMajorCumulativeKeysDescending totalWidth keys) :
    (keys.map (input.ruleMajorPrefixObservable width)).Pairwise
      (fun left right => compareRuleMajorPrefixObservable left right ≠ Ordering.lt) := by
  unfold RuleMajorCumulativeKeysDescending at descending
  induction keys with
  | nil => simp
  | cons head tail ih =>
      rcases List.pairwise_cons.mp descending with ⟨headNotLt, tailDescending⟩
      simp only [List.map_cons, List.pairwise_cons]
      constructor
      · intro observed present
        obtain ⟨original, originalPresent, rfl⟩ := List.mem_map.mp present
        intro prefixLt
        apply headNotLt original originalPresent
        have shortLt : input.compareRuleMajorCumulativeDescriptor width head original = Ordering.lt := by
          rw [← input.compareRuleMajorPrefixObservable_key_eq width head original]
          exact prefixLt
        rw [widthPlus]
        exact input.compareRuleMajorCumulativeDescriptor_prefix_preserves
          width extra head original shortLt
      · exact ih tailDescending

theorem ruleMajorPrefixObservable_sort_perm (input : CertifiedLocalizedCIPInput)
    (width : Nat) (keys : List input.LocalizedRerootCumulativeRule45Key) :
    ((sortKeysBy (input.compareRuleMajorCumulativeDescriptor width) keys).map
      (input.ruleMajorPrefixObservable width)).Perm
      (keys.map (input.ruleMajorPrefixObservable width)) :=
  (input.sortKeysBy_ruleMajorCumulative_perm width keys).map _

theorem ruleMajorPrefixObservable_sort_pairwise (input : CertifiedLocalizedCIPInput)
    (width : Nat) (keys : List input.LocalizedRerootCumulativeRule45Key) :
    ((sortKeysBy (input.compareRuleMajorCumulativeDescriptor width) keys).map
      (input.ruleMajorPrefixObservable width)).Pairwise
      (fun left right => compareRuleMajorPrefixObservable left right ≠ Ordering.lt) := by
  exact input.ruleMajorPrefixObservable_pairwise_of_descending
    (width := width) (totalWidth := width) (extra := 0) (by simp) _
    (input.sortKeysBy_ruleMajorCumulative_descending width keys)

theorem ruleMajorPrefixObservable_sorted_perm_unique
    (left right : List (RuleMajorPrefixObservable V))
    (permutation : left.Perm right)
    (leftDescending : left.Pairwise
      (fun a b => compareRuleMajorPrefixObservable a b ≠ Ordering.lt))
    (rightDescending : right.Pairwise
      (fun a b => compareRuleMajorPrefixObservable a b ≠ Ordering.lt)) :
    left = right := by
  letI : Std.TransCmp (@compareRuleMajorPrefixObservable V) :=
    compareRuleMajorPrefixObservable_transCmp
  exact List.Perm.eq_of_pairwise
    (le := fun left right => compareRuleMajorPrefixObservable left right ≠ Ordering.lt)
    (fun a b _ _ lower upper =>
      (compareRuleMajorPrefixObservable_eq_iff a b).mp (by
        refine Ordering.eq_eq_of_isLE_of_isGE ?_ (Ordering.ne_lt_iff_isGE.mp lower)
        rw [← Std.OrientedCmp.isGE_eq_isLE]
        exact Ordering.ne_lt_iff_isGE.mp upper))
    leftDescending rightDescending permutation

theorem sort_ruleMajorPrefixObservable_eq_of_same_input
    (input : CertifiedLocalizedCIPInput) (width extra : Nat)
    (leftKeys rightKeys : List input.LocalizedRerootCumulativeRule45Key)
    (sameInput : leftKeys.map (input.ruleMajorPrefixObservable width) =
      rightKeys.map (input.ruleMajorPrefixObservable width)) :
    (sortKeysBy (input.compareRuleMajorCumulativeDescriptor width) leftKeys).map
        (input.ruleMajorPrefixObservable width) =
      (sortKeysBy (input.compareRuleMajorCumulativeDescriptor (width + extra)) rightKeys).map
        (input.ruleMajorPrefixObservable width) := by
  let leftSorted := sortKeysBy (input.compareRuleMajorCumulativeDescriptor width) leftKeys
  let rightSorted := sortKeysBy
    (input.compareRuleMajorCumulativeDescriptor (width + extra)) rightKeys
  have leftPerm : (leftSorted.map (input.ruleMajorPrefixObservable width)).Perm
      (leftKeys.map (input.ruleMajorPrefixObservable width)) :=
    (input.sortKeysBy_ruleMajorCumulative_perm width leftKeys).map _
  have rightPerm : (rightSorted.map (input.ruleMajorPrefixObservable width)).Perm
      (rightKeys.map (input.ruleMajorPrefixObservable width)) :=
    (input.sortKeysBy_ruleMajorCumulative_perm (width + extra) rightKeys).map _
  have samePerm : (leftSorted.map (input.ruleMajorPrefixObservable width)).Perm
      (rightSorted.map (input.ruleMajorPrefixObservable width)) :=
    leftPerm.trans ((List.Perm.of_eq sameInput).trans rightPerm.symm)
  have leftDescending : (leftSorted.map (input.ruleMajorPrefixObservable width)).Pairwise
      (fun a b => compareRuleMajorPrefixObservable a b ≠ Ordering.lt) := by
    simpa [leftSorted] using input.ruleMajorPrefixObservable_sort_pairwise width leftKeys
  have rightDescending : (rightSorted.map (input.ruleMajorPrefixObservable width)).Pairwise
      (fun a b => compareRuleMajorPrefixObservable a b ≠ Ordering.lt) := by
    simpa [rightSorted] using input.ruleMajorPrefixObservable_pairwise_of_descending
      (width := width) (totalWidth := width + extra) (extra := extra) rfl rightSorted
      (input.sortKeysBy_ruleMajorCumulative_descending (width + extra) rightKeys)
  exact ruleMajorPrefixObservable_sorted_perm_unique _ _
    samePerm leftDescending rightDescending

private def mergeSparseLayerTables {α : Type*}
    (tables : List (List (List (OfficialSparseEntry α)))) :
    List (List (OfficialSparseEntry α)) :=
  let count := tables.foldl (fun longest table => max longest table.length) 0
  (List.range count).map fun depth =>
    tables.zipIdx.flatMap fun table =>
      OfficialRuleMajorKey.prefixLayer table.2 (table.1.getD depth [])

private theorem zipIdx_map_eq {α β : Type*} (f : α → β) :
    ∀ values : List α, ∀ start : Nat,
      (values.map f).zipIdx start = (values.zipIdx start).map (fun item => (f item.1, item.2))
  | [], _ => rfl
  | value :: values, start => by
      simp [zipIdx_map_eq f values (start + 1)]

private theorem mergeChildren_eq_mergeSparseLayerTables {V α : Type*}
    (children : List (OfficialRuleMajorKey V))
    (layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α))) :
    OfficialRuleMajorKey.mergeChildren children layers =
      mergeSparseLayerTables (children.map layers) := by
  unfold OfficialRuleMajorKey.mergeChildren OfficialRuleMajorKey.childLayerCount
    mergeSparseLayerTables
  rw [zipIdx_map_eq layers children 0]
  simp [List.foldl_map, List.flatMap_map]

private theorem projectCumulative_length (index : Nat)
    (layers : List (List (OfficialSparseEntry (List Nat)))) :
    (projectCumulative index layers).length = layers.length := by
  simp [projectCumulative]

private def projectCumulativeLayer (index : Nat)
    (layer : List (OfficialSparseEntry (List Nat))) : List (OfficialSparseEntry Nat) :=
  layer.map fun entry => (entry.1, entry.2.getD index 0)

private theorem projectCumulative_getD (index depth : Nat)
    (layers : List (List (OfficialSparseEntry (List Nat)))) :
    (projectCumulative index layers).getD depth [] =
      projectCumulativeLayer index (layers.getD depth []) := by
  change (layers.map (projectCumulativeLayer index)).getD depth [] =
    projectCumulativeLayer index (layers.getD depth [])
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases layers[depth]? <;> rfl

private theorem projectCumulative_append (index : Nat)
    (left right : List (List (OfficialSparseEntry (List Nat)))) :
    projectCumulative index (left ++ right) =
      projectCumulative index left ++ projectCumulative index right := by
  simp [projectCumulative]

private theorem projectCumulative_mergeSparseLayerTables (index : Nat)
    (tables : List (List (List (OfficialSparseEntry (List Nat))))) :
    projectCumulative index (mergeSparseLayerTables tables) =
      mergeSparseLayerTables (tables.map (projectCumulative index)) := by
  unfold projectCumulative mergeSparseLayerTables
  rw [zipIdx_map_eq
    (fun layers => layers.map (List.map fun entry => (entry.1, entry.2.getD index 0))) tables 0]
  have countEq :
      (tables.map (List.map (List.map fun entry => (entry.1, entry.2.getD index 0)))).foldl
          (fun longest table => max longest table.length) 0 =
        tables.foldl (fun longest table => max longest table.length) 0 := by
    simp [List.foldl_map, List.length_map]
  rw [countEq]
  rw [List.map_map]
  apply List.map_congr_left
  intro depth hdepth
  simp only [Function.comp_apply, List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro item itemMem
  cases item with
  | mk table slot =>
      change (projectCumulativeLayer index
        (OfficialRuleMajorKey.prefixLayer slot (table.getD depth []))) =
        OfficialRuleMajorKey.prefixLayer slot ((projectCumulative index table).getD depth [])
      rw [projectCumulative_getD]
      simp [projectCumulativeLayer, OfficialRuleMajorKey.prefixLayer,
        List.map_map, Function.comp_def]

private theorem mapM_ruleMajorPrefixObservable_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} (width : Nat)
    (f g : input.LocalizedRerootCursor carrierFuel →
      Option input.LocalizedRerootCumulativeRule45Key)
    (sameAt : ∀ cursor left right, f cursor = some left → g cursor = some right →
      input.ruleMajorPrefixObservable width left = input.ruleMajorPrefixObservable width right) :
    ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel))
      (left right : List input.LocalizedRerootCumulativeRule45Key),
      cursors.mapM f = some left → cursors.mapM g = some right →
      left.map (input.ruleMajorPrefixObservable width) =
        right.map (input.ruleMajorPrefixObservable width)
  | [], left, right, leftComputed, rightComputed => by
      simp at leftComputed rightComputed
      subst left
      subst right
      rfl
  | cursor :: cursors, left, right, leftComputed, rightComputed => by
      rw [List.mapM_cons] at leftComputed rightComputed
      obtain ⟨leftHead, leftHeadComputed, leftContinue⟩ :=
        Option.bind_eq_some_iff.mp leftComputed
      obtain ⟨rightHead, rightHeadComputed, rightContinue⟩ :=
        Option.bind_eq_some_iff.mp rightComputed
      obtain ⟨leftTail, leftTailComputed⟩ :
          ∃ tail, List.mapM f cursors = some tail := by
        cases htail : List.mapM f cursors with
        | none => simp [htail] at leftContinue
        | some tail =>
            exact ⟨tail, rfl⟩
      obtain ⟨rightTail, rightTailComputed⟩ :
          ∃ tail, List.mapM g cursors = some tail := by
        cases htail : List.mapM g cursors with
        | none => simp [htail] at rightContinue
        | some tail =>
            exact ⟨tail, rfl⟩
      have leftEq : leftHead :: leftTail = left := by
        apply Option.some.inj
        simpa [leftTailComputed] using leftContinue
      have rightEq : rightHead :: rightTail = right := by
        apply Option.some.inj
        simpa [rightTailComputed] using rightContinue
      have headEq := sameAt cursor leftHead rightHead leftHeadComputed rightHeadComputed
      have tailEq := mapM_ruleMajorPrefixObservable_eq input width f g sameAt
        cursors _ _ leftTailComputed rightTailComputed
      rw [← leftEq, ← rightEq]
      simp [headEq, tailEq]

private theorem ruleMajorColumns_getD_eq (input : CertifiedLocalizedCIPInput)
    (width index : Nat) (indexLt : index < width)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    (input.ruleMajorCumulativeColumns width key).getD index [] =
      projectCumulative index key.descriptor := by
  unfold ruleMajorCumulativeColumns
  simp [List.getD_eq_getElem?_getD, indexLt]

private theorem mergeLocalizedDescriptor_eq_mergeSparse (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootCumulativeRule45Key) :
    input.mergeLocalizedRerootDescriptorChildren keys =
      mergeSparseLayerTables (keys.map fun key => key.descriptor) := by
  unfold mergeLocalizedRerootDescriptorChildren localizedRerootDescriptorChildLayerCount
    mergeSparseLayerTables
  rw [zipIdx_map_eq (fun key => key.descriptor) keys 0]
  simp [List.foldl_map, List.flatMap_map]

private theorem sameObservable_map_ruleLayers {input : CertifiedLocalizedCIPInput}
    {width : Nat} {left right : List input.LocalizedRerootCumulativeRule45Key}
    (same : left.map (input.ruleMajorPrefixObservable width) =
      right.map (input.ruleMajorPrefixObservable width)) :
    left.map (fun key => key.constitutional.rule1a) =
      right.map (fun key => key.constitutional.rule1a) ∧
    left.map (fun key => key.constitutional.rule1b) =
      right.map (fun key => key.constitutional.rule1b) ∧
    left.map (fun key => key.constitutional.rule2) =
      right.map (fun key => key.constitutional.rule2) := by
  constructor
  · have h := congrArg (List.map RuleMajorPrefixObservable.rule1a) same
    simpa [ruleMajorPrefixObservable] using h
  constructor
  · have h := congrArg (List.map RuleMajorPrefixObservable.rule1b) same
    simpa [ruleMajorPrefixObservable] using h
  · have h := congrArg (List.map RuleMajorPrefixObservable.rule2) same
    simpa [ruleMajorPrefixObservable] using h

private theorem sameObservable_map_projectedDescriptor {input : CertifiedLocalizedCIPInput}
    {width index : Nat} (indexLt : index < width)
    {left right : List input.LocalizedRerootCumulativeRule45Key}
    (same : left.map (input.ruleMajorPrefixObservable width) =
      right.map (input.ruleMajorPrefixObservable width)) :
    left.map (fun key => projectCumulative index key.descriptor) =
      right.map (fun key => projectCumulative index key.descriptor) := by
  have h := congrArg (List.map fun observable => observable.columns.getD index []) same
  simp only [List.map_map] at h
  have hleft : left.map (fun key => (input.ruleMajorCumulativeColumns width key).getD index []) =
      left.map (fun key => projectCumulative index key.descriptor) := by
    apply List.map_congr_left
    intro key _
    exact ruleMajorColumns_getD_eq input width index indexLt key
  have hright : right.map (fun key => (input.ruleMajorCumulativeColumns width key).getD index []) =
      right.map (fun key => projectCumulative index key.descriptor) := by
    apply List.map_congr_left
    intro key _
    exact ruleMajorColumns_getD_eq input width index indexLt key
  exact hleft.symm.trans (h.trans hright)

private theorem prefixObservable_step_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} (width : Nat)
    (earlier later : LocalizedCumulativeRule45Stage)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (label : Option LocalizedAuxiliaryLabel)
    (leftChildren rightChildren : List input.LocalizedRerootCumulativeRule45Key)
    (sameChildren : leftChildren.map (input.ruleMajorPrefixObservable width) =
      rightChildren.map (input.ruleMajorPrefixObservable width))
    (priorityPrefix : ∀ observed index, index < width →
      (localizedCumulativeRule45Priority earlier observed).getD index 0 =
        (localizedCumulativeRule45Priority later observed).getD index 0) :
    input.ruleMajorPrefixObservable width
        (localizedCumulativeRule45StepKey input earlier cursor label leftChildren) =
      input.ruleMajorPrefixObservable width
        (localizedCumulativeRule45StepKey input later cursor label rightChildren) := by
  have hlayers := sameObservable_map_ruleLayers sameChildren
  have hprojected : ∀ index, index < width →
      leftChildren.map (fun key => projectCumulative index key.descriptor) =
        rightChildren.map (fun key => projectCumulative index key.descriptor) := by
    intro index indexLt
    exact sameObservable_map_projectedDescriptor indexLt sameChildren
  have hpriority : ∀ index, index < width →
      projectCumulative index [[([], localizedCumulativeRule45Priority earlier label)]] =
        projectCumulative index [[([], localizedCumulativeRule45Priority later label)]] := by
    intro index indexLt
    change [[([], (localizedCumulativeRule45Priority earlier label).getD index 0)]] =
      [[([], (localizedCumulativeRule45Priority later label).getD index 0)]]
    rw [priorityPrefix label index indexLt]
  change (input.ruleMajorPrefixObservable width
      (localizedCumulativeRule45StepKey input earlier cursor label leftChildren)) =
    (input.ruleMajorPrefixObservable width
      (localizedCumulativeRule45StepKey input later cursor label rightChildren))
  simp only [ruleMajorPrefixObservable, localizedCumulativeRule45StepKey]
  rw [RuleMajorPrefixObservable.mk.injEq]
  constructor
  · change (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false).rule1a ++
        OfficialRuleMajorKey.mergeChildren (leftChildren.map fun key => key.constitutional)
          OfficialRuleMajorKey.rule1a =
      (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false).rule1a ++
        OfficialRuleMajorKey.mergeChildren (rightChildren.map fun key => key.constitutional)
          OfficialRuleMajorKey.rule1a
    have hmap : (leftChildren.map fun key => key.constitutional).map
        OfficialRuleMajorKey.rule1a =
        (rightChildren.map fun key => key.constitutional).map OfficialRuleMajorKey.rule1a := by
      simpa only [List.map_map] using hlayers.1
    exact congrArg (List.append
      (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false).rule1a)
      (CompilerProjectionFidelity.mergeChildren_eq_of_map_layers_eq
        (leftChildren.map fun key => key.constitutional)
        (rightChildren.map fun key => key.constitutional)
        OfficialRuleMajorKey.rule1a hmap)
  constructor
  · change (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false).rule1b ++
        OfficialRuleMajorKey.mergeChildren (leftChildren.map fun key => key.constitutional)
          OfficialRuleMajorKey.rule1b =
      (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false).rule1b ++
        OfficialRuleMajorKey.mergeChildren (rightChildren.map fun key => key.constitutional)
          OfficialRuleMajorKey.rule1b
    have hmap : (leftChildren.map fun key => key.constitutional).map
        OfficialRuleMajorKey.rule1b =
        (rightChildren.map fun key => key.constitutional).map OfficialRuleMajorKey.rule1b := by
      simpa only [List.map_map] using hlayers.2.1
    exact congrArg (List.append
      (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false).rule1b)
      (CompilerProjectionFidelity.mergeChildren_eq_of_map_layers_eq
        (leftChildren.map fun key => key.constitutional)
        (rightChildren.map fun key => key.constitutional)
        OfficialRuleMajorKey.rule1b hmap)
  constructor
  · change (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false).rule2 ++
        OfficialRuleMajorKey.mergeChildren (leftChildren.map fun key => key.constitutional)
          OfficialRuleMajorKey.rule2 =
      (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false).rule2 ++
        OfficialRuleMajorKey.mergeChildren (rightChildren.map fun key => key.constitutional)
          OfficialRuleMajorKey.rule2
    have hmap : (leftChildren.map fun key => key.constitutional).map
        OfficialRuleMajorKey.rule2 =
        (rightChildren.map fun key => key.constitutional).map OfficialRuleMajorKey.rule2 := by
      simpa only [List.map_map] using hlayers.2.2
    exact congrArg (List.append
      (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false).rule2)
      (CompilerProjectionFidelity.mergeChildren_eq_of_map_layers_eq
        (leftChildren.map fun key => key.constitutional)
        (rightChildren.map fun key => key.constitutional)
        OfficialRuleMajorKey.rule2 hmap)
  · apply List.ext_getElem (by simp [ruleMajorCumulativeColumns])
    intro index leftBound rightBound
    have indexLtWidth : index < width := by
      simpa [ruleMajorCumulativeColumns] using leftBound
    have hdesc : projectCumulative index
          ([[([], localizedCumulativeRule45Priority earlier label)]] ++
            input.mergeLocalizedRerootDescriptorChildren leftChildren) =
        projectCumulative index
          ([[([], localizedCumulativeRule45Priority later label)]] ++
            input.mergeLocalizedRerootDescriptorChildren rightChildren) := by
      rw [projectCumulative_append, projectCumulative_append]
      rw [hpriority index indexLtWidth]
      rw [mergeLocalizedDescriptor_eq_mergeSparse input leftChildren,
        mergeLocalizedDescriptor_eq_mergeSparse input rightChildren]
      rw [projectCumulative_mergeSparseLayerTables index
          (leftChildren.map fun key => key.descriptor)]
      rw [projectCumulative_mergeSparseLayerTables index
          (rightChildren.map fun key => key.descriptor)]
      congr 1
      exact congrArg mergeSparseLayerTables (by
        simpa only [List.map_map] using hprojected index indexLtWidth)
    simpa [ruleMajorCumulativeColumns, List.getElem_map, List.getElem_range]
      using hdesc

private theorem prefixObservable_terminal_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} (width : Nat)
    (earlier later : LocalizedCumulativeRule45Stage)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (label : Option LocalizedAuxiliaryLabel)
    (priorityPrefix : ∀ observed index, index < width →
      (localizedCumulativeRule45Priority earlier observed).getD index 0 =
        (localizedCumulativeRule45Priority later observed).getD index 0) :
    input.ruleMajorPrefixObservable width
        (localizedCumulativeRule45TerminalKey input earlier cursor label) =
      input.ruleMajorPrefixObservable width
        (localizedCumulativeRule45TerminalKey input later cursor label) := by
  simp only [ruleMajorPrefixObservable, localizedCumulativeRule45TerminalKey]
  rw [RuleMajorPrefixObservable.mk.injEq]
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · apply List.ext_getElem (by simp [ruleMajorCumulativeColumns])
    intro index leftBound rightBound
    have indexLt : index < width := by
      simpa [ruleMajorCumulativeColumns] using leftBound
    simp only [ruleMajorCumulativeColumns, List.getElem_map, List.getElem_range]
    simp only [projectCumulative]
    exact congrArg (fun value => [[([], value)]])
      (priorityPrefix label index indexLt)

/-- Successful recursive builds at two stages have identical constitutional observations and
identical complete descriptor columns through `width`, provided the later stage only appends
priority components. -/
theorem buildRuleMajorCumulativeWithRead_prefixObservable_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (earlier later : LocalizedCumulativeRule45Stage) (width extra : Nat)
    (earlierWidth : ruleMajorStageWidth earlier = width)
    (laterWidth : ruleMajorStageWidth later = width + extra)
    (priorityPrefix : ∀ label index, index < width →
      (localizedCumulativeRule45Priority earlier label).getD index 0 =
        (localizedCumulativeRule45Priority later label).getD index 0)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    ∀ fuel cursor left right,
      input.buildRuleMajorCumulativeWithRead? earlier read fuel cursor = some left →
      input.buildRuleMajorCumulativeWithRead? later read fuel cursor = some right →
      input.ruleMajorPrefixObservable width left = input.ruleMajorPrefixObservable width right := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor left right leftBuilt rightBuilt
      unfold buildRuleMajorCumulativeWithRead? at leftBuilt rightBuilt
      cases childrenResult : input.localizedRerootChildren? cursor with
      | none => simp [childrenResult] at leftBuilt
      | some children =>
          simp only [childrenResult] at leftBuilt rightBuilt
          by_cases empty : children = []
          · have leftEq : localizedCumulativeRule45TerminalKey input earlier cursor
                (read cursor) = left := by simpa [empty] using leftBuilt
            have rightEq : localizedCumulativeRule45TerminalKey input later cursor
                (read cursor) = right := by simpa [empty] using rightBuilt
            rw [← leftEq, ← rightEq]
            exact prefixObservable_terminal_eq input width earlier later cursor (read cursor)
              priorityPrefix
          · simp [empty] at leftBuilt
  | succ fuel ih =>
      intro cursor left right leftBuilt rightBuilt
      unfold buildRuleMajorCumulativeWithRead? at leftBuilt rightBuilt
      cases childrenResult : input.localizedRerootChildren? cursor with
      | none => simp [childrenResult] at leftBuilt
      | some children =>
          simp only [childrenResult] at leftBuilt rightBuilt
          by_cases empty : children = []
          · have leftEq : localizedCumulativeRule45TerminalKey input earlier cursor
                (read cursor) = left := by simpa [empty] using leftBuilt
            have rightEq : localizedCumulativeRule45TerminalKey input later cursor
                (read cursor) = right := by simpa [empty] using rightBuilt
            rw [← leftEq, ← rightEq]
            exact prefixObservable_terminal_eq input width earlier later cursor (read cursor)
              priorityPrefix
          ·
            cases leftChildrenResult :
                children.mapM (input.buildRuleMajorCumulativeWithRead? earlier read fuel) with
            | none => simp [leftChildrenResult, empty] at leftBuilt
            | some leftChildren =>
              cases rightChildrenResult :
                  children.mapM (input.buildRuleMajorCumulativeWithRead? later read fuel) with
              | none => simp [rightChildrenResult, empty] at rightBuilt
              | some rightChildren =>
                have leftEq : localizedCumulativeRule45StepKey input earlier cursor
                    (read cursor) (sortRuleMajorCumulativeKeys input earlier leftChildren) = left := by
                  simpa [leftChildrenResult, empty] using leftBuilt
                have rightEq : localizedCumulativeRule45StepKey input later cursor
                    (read cursor) (sortRuleMajorCumulativeKeys input later rightChildren) = right := by
                  simpa [rightChildrenResult, empty] using rightBuilt
                have childrenObs := mapM_ruleMajorPrefixObservable_eq input width
                  (input.buildRuleMajorCumulativeWithRead? earlier read fuel)
                  (input.buildRuleMajorCumulativeWithRead? later read fuel)
                  (by
                    intro child leftChild rightChild leftChildBuilt rightChildBuilt
                    exact ih child leftChild rightChild leftChildBuilt rightChildBuilt)
                  children leftChildren rightChildren leftChildrenResult rightChildrenResult
                have sortedObs := input.sort_ruleMajorPrefixObservable_eq_of_same_input
                  width extra leftChildren rightChildren childrenObs
                have sortedObs' :
                    (sortRuleMajorCumulativeKeys input earlier leftChildren).map
                        (input.ruleMajorPrefixObservable width) =
                      (sortRuleMajorCumulativeKeys input later rightChildren).map
                        (input.ruleMajorPrefixObservable width) := by
                  change (sortKeysBy (input.compareRuleMajorCumulativeDescriptor
                      (ruleMajorStageWidth earlier)) leftChildren).map _ =
                    (sortKeysBy (input.compareRuleMajorCumulativeDescriptor
                      (ruleMajorStageWidth later)) rightChildren).map _
                  rw [earlierWidth, laterWidth]
                  exact sortedObs
                rw [← leftEq, ← rightEq]
                exact prefixObservable_step_eq input width earlier later cursor (read cursor)
                  (sortRuleMajorCumulativeKeys input earlier leftChildren)
                  (sortRuleMajorCumulativeKeys input later rightChildren) sortedObs'
                  priorityPrefix

private theorem rule4a_rule4b_priority_prefix (reference : RS) :
    ∀ label index, index < 1 →
      (localizedCumulativeRule45Priority .rule4a label).getD index 0 =
        (localizedCumulativeRule45Priority (.rule4b reference) label).getD index 0 := by
  intro label index bound
  interval_cases index; all_goals rfl

private theorem rule4b_rule4c_priority_prefix (reference : RS) :
    ∀ label index, index < 2 →
      (localizedCumulativeRule45Priority (.rule4b reference) label).getD index 0 =
        (localizedCumulativeRule45Priority (.rule4c reference) label).getD index 0 := by
  intro label index bound
  interval_cases index; all_goals rfl

private theorem rule4a_rule4cNoReference_priority_prefix :
    ∀ label index, index < 1 →
      (localizedCumulativeRule45Priority .rule4a label).getD index 0 =
        (localizedCumulativeRule45Priority .rule4cNoReference label).getD index 0 := by
  intro label index bound
  interval_cases index; all_goals rfl

/-- The first constitutional/descriptor column is stable when Rule 4b is appended. -/
theorem buildRuleMajorCumulativeWithRead_rule4a_rule4b_prefix
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} (reference : RS)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    ∀ fuel cursor left right,
      input.buildRuleMajorCumulativeWithRead? .rule4a read fuel cursor = some left →
      input.buildRuleMajorCumulativeWithRead? (.rule4b reference) read fuel cursor = some right →
      input.ruleMajorPrefixObservable 1 left = input.ruleMajorPrefixObservable 1 right := by
  exact input.buildRuleMajorCumulativeWithRead_prefixObservable_eq .rule4a
    (.rule4b reference) 1 1 (by simp [ruleMajorStageWidth, localizedCumulativeRule45Priority])
    (by simp [ruleMajorStageWidth, localizedCumulativeRule45Priority])
    (rule4a_rule4b_priority_prefix reference) read

/-- Rule 4b sorting and Rule 4c sorting preserve the same constitutional comparison columns and both earlier
descriptor columns, for every reader and every pair of successful recursive builds. -/
theorem buildRuleMajorCumulativeWithRead_rule4b_rule4c_prefix
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} (reference : RS)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    ∀ fuel cursor left right,
      input.buildRuleMajorCumulativeWithRead? (.rule4b reference) read fuel cursor = some left →
      input.buildRuleMajorCumulativeWithRead? (.rule4c reference) read fuel cursor = some right →
      input.ruleMajorPrefixObservable 2 left = input.ruleMajorPrefixObservable 2 right := by
  exact input.buildRuleMajorCumulativeWithRead_prefixObservable_eq (.rule4b reference)
    (.rule4c reference) 2 1 (by simp [ruleMajorStageWidth, localizedCumulativeRule45Priority])
    (by simp [ruleMajorStageWidth, localizedCumulativeRule45Priority])
    (rule4b_rule4c_priority_prefix reference) read

/-- The first Rule 4a descriptor column is stable when the no-reference Rule 4c rank is added. -/
theorem buildRuleMajorCumulativeWithRead_rule4a_rule4cNoReference_prefix
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    ∀ fuel cursor left right,
      input.buildRuleMajorCumulativeWithRead? .rule4a read fuel cursor = some left →
      input.buildRuleMajorCumulativeWithRead? .rule4cNoReference read fuel cursor = some right →
      input.ruleMajorPrefixObservable 1 left = input.ruleMajorPrefixObservable 1 right := by
  exact input.buildRuleMajorCumulativeWithRead_prefixObservable_eq .rule4a
    .rule4cNoReference 1 1 (by simp [ruleMajorStageWidth, localizedCumulativeRule45Priority])
    (by simp [ruleMajorStageWidth, localizedCumulativeRule45Priority])
    rule4a_rule4cNoReference_priority_prefix read

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithRead_prefixObservable_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithRead_rule4a_rule4b_prefix
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithRead_rule4b_rule4c_prefix
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithRead_rule4a_rule4cNoReference_prefix

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
