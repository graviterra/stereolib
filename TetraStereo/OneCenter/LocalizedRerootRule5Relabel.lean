import TetraStereo.OneCenter.LocalizedRerootCompoundRule45OutcomeOrder
import TetraStereo.OneCenter.OfficialRuleMajorCompilerProjectionFidelity
import TetraStereo.KernelOnly

set_option autoImplicit false























namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open OfficialRuleMajorKey
open CompilerProjectionFidelity

/-! ## Vectors -/

/-- The Rule-5 bit appended to a stage-4c vector `[a, b, c]`. -/
def rule5Bit (same : Bool) : List Nat → Nat
  | [a, b, _] => if a = 2 then (if same then b else 1 - b) else 0
  | _ => 0

def rule5Lift (same : Bool) (vector : List Nat) : List Nat :=
  vector ++ [rule5Bit same vector]

theorem rule5Lift_priority (rule4bReference rule5Reference : RS)
    (label : Option LocalizedAuxiliaryLabel) :
    localizedCumulativeRule45Priority (.rule5 rule4bReference rule5Reference) label =
      rule5Lift (rule5Reference == rule4bReference)
        (localizedCumulativeRule45Priority (.rule4c rule4bReference) label) := by
  cases label with
  | none => cases rule4bReference <;> cases rule5Reference <;> rfl
  | some value =>
      cases value with
      | chiral descriptor => cases descriptor <;> cases rule4bReference <;> cases rule5Reference <;> rfl
      | pseudoasymmetric descriptor =>
          cases descriptor <;> cases rule4bReference <;> cases rule5Reference <;> rfl

theorem priority_rule4c_length (reference : RS) (label : Option LocalizedAuxiliaryLabel) :
    (localizedCumulativeRule45Priority (.rule4c reference) label).length = 3 := by
  cases label with
  | none => rfl
  | some value => cases value <;> rfl

private theorem compareLex_append_single (cmp : Nat → Nat → Ordering) :
    ∀ (xs ys : List Nat) (x y : Nat), xs.length = ys.length →
      List.compareLex cmp (xs ++ [x]) (ys ++ [y]) = (List.compareLex cmp xs ys).then (cmp x y)
  | [], [], x, y, _ => by
      simp only [List.nil_append, List.compareLex]
      cases cmp x y <;> rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: xs, b :: ys, x, y, h => by
      simp only [List.cons_append, List.compareLex]
      rw [compareLex_append_single cmp xs ys x y (by simpa using h)]
      cases cmp a b <;> simp [Ordering.then]

private theorem compareNat_sound (left right : ℕ) (h : compareNat left right = Ordering.eq) :
    left = right :=
  (compareNat_eq_eq_iff left right).1 h

theorem compareLocalizedCumulativeRule45Priority_rule5Lift (same : Bool) (v w : List Nat)
    (hv : v.length = 3) (hw : w.length = 3) :
    compareLocalizedCumulativeRule45Priority (rule5Lift same v) (rule5Lift same w) =
      compareLocalizedCumulativeRule45Priority v w := by
  unfold compareLocalizedCumulativeRule45Priority rule5Lift
  rw [compareLex_append_single _ v w _ _ (hv.trans hw.symm)]
  rcases h : List.compareLex compareNat v w with _ | _ | _
  · rfl
  · have : v = w :=
      (list_compareLex_eq_eq_iff compareNat compareNat_self compareNat_sound v w).1 h
    subst this
    simp [Ordering.then, compareNat_self]
  · rfl

/-! ## Layers and keys -/

def rule5LiftLayer (same : Bool) (layer : List (OfficialSparseEntry (List Nat))) :
    List (OfficialSparseEntry (List Nat)) :=
  layer.map fun entry => (entry.1, rule5Lift same entry.2)

variable (input : CertifiedLocalizedCIPInput)

def rule5LiftKey (same : Bool) (key : input.LocalizedRerootCumulativeRule45Key) :
    input.LocalizedRerootCumulativeRule45Key :=
  { key with descriptor := key.descriptor.map (rule5LiftLayer same) }

/-- Every descriptor entry is a three-component vector (the stage-4c shape). -/
def Stage4cShaped (key : input.LocalizedRerootCumulativeRule45Key) : Prop :=
  ∀ layer ∈ key.descriptor, ∀ entry ∈ layer, entry.2.length = 3

private theorem compareLex_map_rel_mem {α β : Type*} (cmpα : α → α → Ordering)
    (cmpβ : β → β → Ordering) (f : α → β) :
    ∀ xs ys : List α, (∀ x ∈ xs, ∀ y ∈ ys, cmpβ (f x) (f y) = cmpα x y) →
      List.compareLex cmpβ (xs.map f) (ys.map f) = List.compareLex cmpα xs ys
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | x :: xs, y :: ys, h => by
      simp only [List.map_cons, List.compareLex]
      rw [h x List.mem_cons_self y List.mem_cons_self,
        compareLex_map_rel_mem cmpα cmpβ f xs ys fun a ha b hb =>
          h a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem y hb)]

theorem compareSparseEntry_rule5Lift (same : Bool) (e f : OfficialSparseEntry (List Nat))
    (he : e.2.length = 3) (hf : f.2.length = 3) :
    compareSparseEntry compareLocalizedCumulativeRule45Priority
        (e.1, rule5Lift same e.2) (f.1, rule5Lift same f.2) =
      compareSparseEntry compareLocalizedCumulativeRule45Priority e f := by
  unfold compareSparseEntry
  simp only [compareLex, Ordering.byKey]
  rw [compareLocalizedCumulativeRule45Priority_rule5Lift same _ _ he hf]

theorem compareSparseLayer_rule5Lift (same : Bool) (l m : List (OfficialSparseEntry (List Nat)))
    (hl : ∀ e ∈ l, e.2.length = 3) (hm : ∀ e ∈ m, e.2.length = 3) :
    compareSparseLayer compareLocalizedCumulativeRule45Priority
        (rule5LiftLayer same l) (rule5LiftLayer same m) =
      compareSparseLayer compareLocalizedCumulativeRule45Priority l m :=
  compareLex_map_rel_mem _ _ _ l m fun e he f hf =>
    compareSparseEntry_rule5Lift same e f (hl e he) (hm f hf)

theorem compareSparseLayers_rule5Lift (same : Bool)
    (L M : List (List (OfficialSparseEntry (List Nat))))
    (hL : ∀ l ∈ L, ∀ e ∈ l, e.2.length = 3) (hM : ∀ l ∈ M, ∀ e ∈ l, e.2.length = 3) :
    compareSparseLayers compareLocalizedCumulativeRule45Priority
        (L.map (rule5LiftLayer same)) (M.map (rule5LiftLayer same)) =
      compareSparseLayers compareLocalizedCumulativeRule45Priority L M :=
  compareLex_map_rel_mem _ _ _ L M fun l hl m hm =>
    compareSparseLayer_rule5Lift same l m (hL l hl) (hM m hm)

theorem compare_rule5LiftKey (same : Bool) (a b : input.LocalizedRerootCumulativeRule45Key)
    (ha : input.Stage4cShaped a) (hb : input.Stage4cShaped b) :
    input.compareLocalizedRerootCumulativeRule45Keys (input.rule5LiftKey same a)
        (input.rule5LiftKey same b) =
      input.compareLocalizedRerootCumulativeRule45Keys a b := by
  unfold compareLocalizedRerootCumulativeRule45Keys
  simp only [compareLex, Ordering.byKey, rule5LiftKey]
  rw [compareSparseLayers_rule5Lift same _ _ ha hb]

/-! ## The sort and the merges commute with the lift -/

theorem insert_rule5LiftKey (same : Bool) (key : input.LocalizedRerootCumulativeRule45Key)
    (hkey : input.Stage4cShaped key) :
    ∀ keys : List input.LocalizedRerootCumulativeRule45Key, (∀ x ∈ keys, input.Stage4cShaped x) →
      input.insertLocalizedRerootCumulativeRule45Key (input.rule5LiftKey same key)
          (keys.map (input.rule5LiftKey same)) =
        (input.insertLocalizedRerootCumulativeRule45Key key keys).map (input.rule5LiftKey same)
  | [], _ => rfl
  | head :: tail, hkeys => by
      have hc := input.compare_rule5LiftKey same key head hkey (hkeys head List.mem_cons_self)
      simp only [List.map_cons, insertLocalizedRerootCumulativeRule45Key, hc]
      rw [insert_rule5LiftKey same key hkey tail fun x hx => hkeys x (List.mem_cons_of_mem head hx)]
      cases input.compareLocalizedRerootCumulativeRule45Keys key head <;> rfl

theorem sort_rule5LiftKey (same : Bool) :
    ∀ keys : List input.LocalizedRerootCumulativeRule45Key, (∀ x ∈ keys, input.Stage4cShaped x) →
      input.sortLocalizedRerootCumulativeRule45Keys (keys.map (input.rule5LiftKey same)) =
        (input.sortLocalizedRerootCumulativeRule45Keys keys).map (input.rule5LiftKey same)
  | [], _ => rfl
  | key :: tail, hkeys => by
      have tailShaped : ∀ x ∈ tail, input.Stage4cShaped x :=
        fun x hx => hkeys x (List.mem_cons_of_mem key hx)
      simp only [List.map_cons, sortLocalizedRerootCumulativeRule45Keys]
      rw [sort_rule5LiftKey same tail tailShaped,
        input.insert_rule5LiftKey same key (hkeys key List.mem_cons_self) _ fun x hx =>
          tailShaped x ((input.sortLocalizedRerootCumulativeRule45Keys_perm tail).mem_iff.1 hx)]

theorem rankedChildTail_rule5LiftKey (same : Bool)
    (previous : input.LocalizedRerootCumulativeRule45Key) (hprevious : input.Stage4cShaped previous)
    (rank : Nat) :
    ∀ keys : List input.LocalizedRerootCumulativeRule45Key, (∀ x ∈ keys, input.Stage4cShaped x) →
      input.localizedRerootRankedChildTail (input.rule5LiftKey same previous) rank
          (keys.map (input.rule5LiftKey same)) =
        (input.localizedRerootRankedChildTail previous rank keys).map
          (Prod.map (input.rule5LiftKey same) id)
  | [], _ => rfl
  | child :: tail, hkeys => by
      have hc := input.compare_rule5LiftKey same child previous (hkeys child List.mem_cons_self)
        hprevious
      simp only [List.map_cons, localizedRerootRankedChildTail, hc]
      rw [rankedChildTail_rule5LiftKey same child (hkeys child List.mem_cons_self) _ tail
        fun x hx => hkeys x (List.mem_cons_of_mem child hx)]
      rfl

theorem rankedChildren_rule5LiftKey (same : Bool) :
    ∀ keys : List input.LocalizedRerootCumulativeRule45Key, (∀ x ∈ keys, input.Stage4cShaped x) →
      input.localizedRerootRankedChildren (keys.map (input.rule5LiftKey same)) =
        (input.localizedRerootRankedChildren keys).map (Prod.map (input.rule5LiftKey same) id)
  | [], _ => rfl
  | child :: tail, hkeys => by
      simp only [List.map_cons, localizedRerootRankedChildren]
      rw [input.rankedChildTail_rule5LiftKey same child (hkeys child List.mem_cons_self) 0 tail
        fun x hx => hkeys x (List.mem_cons_of_mem child hx)]
      rfl

private theorem zipIdx_map' {α β : Type*} (f : α → β) :
    ∀ (l : List α) (n : Nat), (l.map f).zipIdx n = (l.zipIdx n).map (Prod.map f id)
  | [], _ => rfl
  | a :: l, n => by
      simp only [List.map_cons, List.zipIdx_cons]
      rw [zipIdx_map' f l (n + 1)]
      rfl

private theorem getD_liftLayer (same : Bool) (L : List (List (OfficialSparseEntry (List Nat))))
    (n : Nat) :
    (L.map (rule5LiftLayer same)).getD n [] = rule5LiftLayer same (L.getD n []) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[n]? <;> rfl

private theorem prefixLayer_liftLayer (same : Bool) (slot : Nat)
    (layer : List (OfficialSparseEntry (List Nat))) :
    prefixLayer slot (rule5LiftLayer same layer) = rule5LiftLayer same (prefixLayer slot layer) := by
  simp only [prefixLayer, rule5LiftLayer, List.map_map]
  rfl

theorem descriptorChildLayerCount_rule5LiftKey (same : Bool)
    (keys : List input.LocalizedRerootCumulativeRule45Key) :
    input.localizedRerootDescriptorChildLayerCount (keys.map (input.rule5LiftKey same)) =
      input.localizedRerootDescriptorChildLayerCount keys := by
  unfold localizedRerootDescriptorChildLayerCount
  rw [List.foldl_map]
  simp [rule5LiftKey]

theorem mergeDescriptor_rule5LiftKey (same : Bool)
    (keys : List input.LocalizedRerootCumulativeRule45Key) :
    input.mergeLocalizedRerootDescriptorChildren (keys.map (input.rule5LiftKey same)) =
      (input.mergeLocalizedRerootDescriptorChildren keys).map (rule5LiftLayer same) := by
  unfold mergeLocalizedRerootDescriptorChildren
  simp only [descriptorChildLayerCount_rule5LiftKey, List.map_map]
  congr 1
  funext depth
  rw [zipIdx_map', List.flatMap_map]
  simp only [Function.comp, rule5LiftLayer, List.map_flatMap]
  congr 1
  funext child
  show prefixLayer child.2 ((child.1.descriptor.map (rule5LiftLayer same)).getD depth []) = _
  rw [getD_liftLayer, prefixLayer_liftLayer]
  rfl

theorem mergeLabel_rule5LiftKey (same : Bool)
    (keys : List input.LocalizedRerootCumulativeRule45Key) :
    input.mergeLocalizedRerootLabelChildren (keys.map (input.rule5LiftKey same)) =
      input.mergeLocalizedRerootLabelChildren keys := by
  simp only [mergeLocalizedRerootLabelChildren, localizedRerootLabelChildLayerCount, List.foldl_map]
  congr 1
  funext depth
  rw [zipIdx_map', List.flatMap_map]
  rfl

theorem mergeRankedLabel_rule5LiftKey (same : Bool)
    (keys : List input.LocalizedRerootCumulativeRule45Key) (hkeys : ∀ x ∈ keys, input.Stage4cShaped x) :
    input.mergeLocalizedRerootRankedLabelChildren (keys.map (input.rule5LiftKey same)) =
      input.mergeLocalizedRerootRankedLabelChildren keys := by
  simp only [mergeLocalizedRerootRankedLabelChildren, localizedRerootRankedLabelChildLayerCount,
    List.foldl_map]
  rw [input.rankedChildren_rule5LiftKey same keys hkeys]
  congr 1
  funext depth
  rw [List.flatMap_map]
  rfl

/-! ## Builder facts -/

private theorem mapM_map_option {α β γ : Type*} (f : α → Option β) (g : α → Option γ) (h : β → γ) :
    ∀ l : List α, (∀ a ∈ l, g a = (f a).map h) → l.mapM g = (l.mapM f).map (List.map h)
  | [], _ => rfl
  | a :: l, agree => by
      rw [List.mapM_cons, List.mapM_cons, agree a List.mem_cons_self,
        mapM_map_option f g h l fun x hx => agree x (List.mem_cons_of_mem a hx)]
      cases f a <;> cases l.mapM f <;> rfl

private theorem mem_of_mapM_some {α β : Type*} (f : α → Option β) :
    ∀ (l : List α) (ys : List β), l.mapM f = some ys → ∀ y ∈ ys, ∃ a ∈ l, f a = some y
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
              simp only [hfa, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq] at h
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

private theorem mem_getD_nil {α : Type*} (L : List (List α)) (n : Nat) (x : α)
    (hx : x ∈ L.getD n []) : ∃ layer ∈ L, x ∈ layer := by
  rw [List.getD_eq_getElem?_getD] at hx
  cases h : L[n]? with
  | none => rw [h] at hx; simp at hx
  | some layer =>
      rw [h] at hx
      exact ⟨layer, List.mem_of_getElem? h, hx⟩

variable {carrierFuel : Nat}

theorem buildLocalizedRerootCumulativeRule45Key?_rule4c_shaped (reference : RS)
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.buildLocalizedRerootCumulativeRule45Key? (.rule4c reference) target view fuel cursor =
        some key → input.Stage4cShaped key
  | 0, cursor, key, h => by
      unfold buildLocalizedRerootCumulativeRule45Key? at h
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
      unfold buildLocalizedRerootCumulativeRule45Key? at h
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
                (input.buildLocalizedRerootCumulativeRule45Key? (.rule4c reference) target view fuel) with
            | none => simp [hkeys] at h
            | some childKeys =>
                simp only [hkeys, Option.bind_some, Option.some.injEq] at h
                subst h
                have childShaped : ∀ k ∈ childKeys, input.Stage4cShaped k := fun k hk => by
                  obtain ⟨c, _, hc⟩ := mem_of_mapM_some _ children childKeys hkeys k hk
                  exact buildLocalizedRerootCumulativeRule45Key?_rule4c_shaped reference target view
                    fuel c k hc
                have sortedShaped : ∀ k ∈ input.sortLocalizedRerootCumulativeRule45Keys childKeys,
                    input.Stage4cShaped k := fun k hk =>
                  childShaped k ((input.sortLocalizedRerootCumulativeRule45Keys_perm childKeys).mem_iff.1 hk)
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
                  exact sortedShaped child.1 (fst_mem_of_mem_zipIdx child _ 0 hchild) layer' hlayer'
                    entry' hmem

/-- **The Rule-5 stage is the Rule-4c stage with relabeled descriptor tables.** -/
theorem buildLocalizedRerootCumulativeRule45Key?_rule5 (rule4bReference rule5Reference : RS)
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      input.buildLocalizedRerootCumulativeRule45Key? (.rule5 rule4bReference rule5Reference)
          target view fuel cursor =
        (input.buildLocalizedRerootCumulativeRule45Key? (.rule4c rule4bReference) target view fuel
          cursor).map (input.rule5LiftKey (rule5Reference == rule4bReference))
  | 0, cursor => by
      unfold buildLocalizedRerootCumulativeRule45Key?
      cases hch : input.localizedRerootChildren? cursor with
      | none => rfl
      | some children =>
          simp only [Option.bind_eq_bind, Option.bind_some]
          split
          · simp only [Option.map_some, rule5LiftKey, List.map_cons, List.map_nil, rule5LiftLayer,
              rule5Lift_priority]
          · rfl
  | fuel + 1, cursor => by
      have ih := buildLocalizedRerootCumulativeRule45Key?_rule5 rule4bReference rule5Reference
        target view fuel
      unfold buildLocalizedRerootCumulativeRule45Key?
      cases hch : input.localizedRerootChildren? cursor with
      | none => rfl
      | some children =>
          simp only [Option.bind_eq_bind, Option.bind_some]
          split
          · simp only [Option.map_some, rule5LiftKey, List.map_cons, List.map_nil, rule5LiftLayer,
              rule5Lift_priority]
          · rw [mapM_map_option _ _ _ children fun c _ => ih c]
            cases hkeys : children.mapM
                (input.buildLocalizedRerootCumulativeRule45Key? (.rule4c rule4bReference) target view
                  fuel) with
            | none => rfl
            | some childKeys =>
                have childShaped : ∀ k ∈ childKeys, input.Stage4cShaped k := fun k hk => by
                  obtain ⟨c, _, hc⟩ := mem_of_mapM_some _ children childKeys hkeys k hk
                  exact input.buildLocalizedRerootCumulativeRule45Key?_rule4c_shaped rule4bReference
                    target view fuel c k hc
                have sortedShaped : ∀ k ∈ input.sortLocalizedRerootCumulativeRule45Keys childKeys,
                    input.Stage4cShaped k := fun k hk =>
                  childShaped k ((input.sortLocalizedRerootCumulativeRule45Keys_perm childKeys).mem_iff.1 hk)
                simp only [Option.map_some, Option.bind_some, Option.some.injEq]
                rw [input.sort_rule5LiftKey _ childKeys childShaped,
                  input.mergeDescriptor_rule5LiftKey, input.mergeLabel_rule5LiftKey,
                  input.mergeRankedLabel_rule5LiftKey _ _ sortedShaped]
                simp only [rule5LiftKey, List.map_map, List.map_append, List.map_cons, List.map_nil,
                  rule5LiftLayer, rule5Lift_priority]
                rfl

/-! ## The fully tied two-reference case -/

private theorem buildLocalizedRerootRule5Reading?_prior
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading) (reading : input.LocalizedRerootRule5Reading)
    (h : input.buildLocalizedRerootRule5Reading? target view fuel cursor prior = some reading) :
    reading.prior = prior := by
  unfold buildLocalizedRerootRule5Reading? at h
  cases hR : input.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor prior.reference? .R) target view fuel cursor with
  | none => simp [hR] at h
  | some commonR =>
      cases hS : input.buildLocalizedRerootCumulativeRule45Key?
          (localizedRule5StageFor prior.reference? .S) target view fuel cursor with
      | none => simp [hR, hS] at h
      | some commonS =>
          simp only [hR, hS, Option.bind_eq_bind, Option.bind_some,
            Option.some.injEq] at h
          subst h
          rfl

private theorem buildLocalizedRerootRule5Readings?_map_prior
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∀ (priors : List input.LocalizedRerootRule4bcReading)
      (readings : List input.LocalizedRerootRule5Reading),
      input.buildLocalizedRerootRule5Readings? target view fuel cursor priors = some readings →
        readings.map (·.prior) = priors
  | [], readings, h => by
      simp only [buildLocalizedRerootRule5Readings?, Option.some.injEq] at h
      subst h; rfl
  | prior :: priors, readings, h => by
      simp only [buildLocalizedRerootRule5Readings?] at h
      cases hr : input.buildLocalizedRerootRule5Reading? target view fuel cursor prior with
      | none => simp [hr] at h
      | some reading =>
          cases hrs : input.buildLocalizedRerootRule5Readings? target view fuel cursor priors with
          | none => simp [hr, hrs] at h
          | some rest =>
              simp only [hr, hrs, Option.bind_eq_bind, Option.bind_some,
                Option.some.injEq] at h
              subst h
              simp only [List.map_cons, List.cons.injEq]
              exact ⟨input.buildLocalizedRerootRule5Reading?_prior target view fuel cursor prior
                reading hr, buildLocalizedRerootRule5Readings?_map_prior target view fuel cursor
                priors rest hrs⟩

theorem localizedRule4bReferencesFromPopulation_eq_of_length_two (descriptors : List RS)
    (h : (localizedRule4bReferencesFromPopulation descriptors).length = 2) :
    localizedRule4bReferencesFromPopulation descriptors = [RS.R, RS.S] := by
  revert h
  unfold localizedRule4bReferencesFromPopulation
  dsimp only
  split_ifs <;> simp

private theorem compareSparseLayers_eq_of_eq (L M : List (List (OfficialSparseEntry (List Nat))))
    (h : compareSparseLayers compareLocalizedCumulativeRule45Priority L M = Ordering.eq) : L = M :=
  (compareSparseLayers_eq_eq_iff compareLocalizedCumulativeRule45Priority
    (fun v => (list_compareLex_eq_eq_iff compareNat compareNat_self compareNat_sound v v).2 rfl)
    (fun v w hvw => (list_compareLex_eq_eq_iff compareNat compareNat_self compareNat_sound v w).1 hvw)
    L M).1 h

private theorem compareSparseLayers_refl (L : List (List (OfficialSparseEntry (List Nat)))) :
    compareSparseLayers compareLocalizedCumulativeRule45Priority L L = Ordering.eq :=
  (compareSparseLayers_eq_eq_iff compareLocalizedCumulativeRule45Priority
    (fun v => (list_compareLex_eq_eq_iff compareNat compareNat_self compareNat_sound v v).2 rfl)
    (fun v w hvw => (list_compareLex_eq_eq_iff compareNat compareNat_self compareNat_sound v w).1 hvw)
    L L).2 rfl

/-- A complete tie of two alternatives forces equal Rule-4c tables. -/
theorem rule4cKey_descriptor_eq_of_complete_eq (a b : input.LocalizedRerootRule4bcReading)
    (h : input.compareRule4bcReadingsComplete a b = Ordering.eq) :
    a.rule4cKey.descriptor = b.rule4cKey.descriptor := by
  unfold compareRule4bcReadingsComplete at h
  simp only [compareLex, Ordering.byKey] at h
  cases h4b : input.compareLocalizedRerootRule4bcReadingsByRule4b a b <;> rw [h4b] at h
  · cases h
  · exact compareSparseLayers_eq_of_eq _ _ h
  · cases h

theorem compareRule4bcReadingsComplete_symm_eq (a b : input.LocalizedRerootRule4bcReading)
    (h : input.compareRule4bcReadingsComplete a b = Ordering.eq) :
    input.compareRule4bcReadingsComplete b a = Ordering.eq := by
  letI := input.compareRule4bcReadingsComplete_transCmp
  rw [Std.OrientedCmp.eq_swap (cmp := input.compareRule4bcReadingsComplete), h]
  rfl

theorem compareRule4bcReadingsComplete_compoundUppercase (a b : input.LocalizedRerootRule4bcReading) :
    input.compareRule4bcReadingsComplete (compoundUppercaseRule4bcReading input a)
        (compoundUppercaseRule4bcReading input b) =
      input.compareRule4bcReadingsComplete a b := rfl

/-- **T1.**  For a built compound key with two alternatives that tie through Rule 4c, the ordered
through-Rule-5 comparison against the ordered key-level mirror image is a complete tie. -/
theorem fullTie_throughRule5_mirror_eq
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule45Key)
    (computed : input.buildLocalizedRerootCompoundRule45Key? target view fuel cursor = some key)
    (two : key.prior.references = [RS.R, RS.S])
    (tie : ∀ a b, key.prior.readings = [a, b] → input.compareRule4bcReadingsComplete a b = .eq) :
    input.compareLocalizedRerootCompoundThroughRule5 (input.outcomeOrdered45 key)
        (input.outcomeOrdered45 (compoundUppercaseCompoundRule45Key input key)) =
      { ordering := .eq, pseudo := false } := by
  -- unfold the compound builder
  unfold buildLocalizedRerootCompoundRule45Key? at computed
  cases hprior : input.buildLocalizedRerootCompoundRule4bcKey? target view fuel cursor with
  | none => simp [hprior] at computed
  | some prior =>
  cases hread : input.buildLocalizedRerootRule5Readings? target view fuel cursor prior.readings with
  | none => simp [hprior, hread] at computed
  | some readings =>
  simp only [hprior, hread, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at computed
  subst computed
  -- the prior
  unfold buildLocalizedRerootCompoundRule4bcKey? at hprior
  cases h4a : input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view fuel cursor with
  | none => simp [h4a] at hprior
  | some rule4aKey =>
  simp only [h4a, Option.bind_eq_bind, Option.bind_some] at hprior
  cases hreads : input.buildLocalizedRerootRule4bcReadings? target view fuel cursor
      (localizedRule4bcReferenceAlternatives
        (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) with
  | none => simp [hreads] at hprior
  | some reads =>
  simp only [hreads, Option.bind_some, Option.some.injEq] at hprior
  subst hprior
  simp only at two tie hread
  rw [two] at hreads
  -- the two alternatives
  simp only [localizedRule4bcReferenceAlternatives, List.map_cons, List.map_nil,
    buildLocalizedRerootRule4bcReadings?, buildLocalizedRerootRule4bcReading?] at hreads
  cases h4bR : input.buildLocalizedRerootCumulativeRule45Key? (.rule4b .R) target view fuel cursor with
  | none => simp [h4bR] at hreads
  | some k4bR =>
  cases h4cR : input.buildLocalizedRerootCumulativeRule45Key? (.rule4c .R) target view fuel cursor with
  | none => simp [h4bR, h4cR] at hreads
  | some k4cR =>
  cases h4bS : input.buildLocalizedRerootCumulativeRule45Key? (.rule4b .S) target view fuel cursor with
  | none => simp [h4bR, h4cR, h4bS] at hreads
  | some k4bS =>
  cases h4cS : input.buildLocalizedRerootCumulativeRule45Key? (.rule4c .S) target view fuel cursor with
  | none => simp [h4bR, h4cR, h4bS, h4cS] at hreads
  | some k4cS =>
  simp only [h4bR, h4cR, h4bS, h4cS, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hreads
  subst hreads
  -- the Rule-5 readings
  simp only [buildLocalizedRerootRule5Readings?, buildLocalizedRerootRule5Reading?,
    localizedRule5StageFor, input.buildLocalizedRerootCumulativeRule45Key?_rule5, h4cR, h4cS,
    Option.map_some, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hread
  subst hread
  -- the complete tie
  have tieRS := tie _ _ rfl
  have tableEq : k4cR.descriptor = k4cS.descriptor :=
    input.rule4cKey_descriptor_eq_of_complete_eq _ _ tieRS
  have tieSR := input.compareRule4bcReadingsComplete_symm_eq _ _ tieRS
  have tieNotLt : input.compareRule4bcReadingsComplete
      { reference? := some RS.R, rule4bKey := k4bR, rule4cKey := k4cR }
      { reference? := some RS.S, rule4bKey := k4bS, rule4cKey := k4cS } ≠ .lt := by
    rw [tieRS]; decide
  have tieNotLt' : input.compareRule4bcReadingsComplete
      { reference? := some RS.S, rule4bKey := k4bS, rule4cKey := k4cS }
      { reference? := some RS.R, rule4bKey := k4bR, rule4cKey := k4cR } ≠ .lt := by
    rw [tieSR]; decide
  -- prior tie from the ordered Rule-4b/4c comparison
  have priorTie := input.outcomeOrdered_reflect_tie
    { rule4aKey := rule4aKey
      references := localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
      referenceCountPriority := constitutionalRule4bReferenceCountPriority
        (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)
      readings := [{ reference? := some RS.R, rule4bKey := k4bR, rule4cKey := k4cR },
        { reference? := some RS.S, rule4bKey := k4bS, rule4cKey := k4cS }] } (by simp)
  unfold compareLocalizedRerootCompoundThroughRule5
  simp only [outcomeOrdered45, compoundUppercaseCompoundRule45Key] at priorTie ⊢
  simp only [priorTie, bne_self_eq_false, Bool.false_eq_true, if_false]
  -- the ordered Rule-5 lists
  simp only [List.map_cons, List.map_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, rankRule5Readings,
    compoundUppercaseRule5Reading, compareRule4bcReadingsComplete_compoundUppercase,
    if_neg tieNotLt, if_neg tieNotLt']
  -- the common-R comparison is a comparison of literally equal tables
  have cmpR : input.compareLocalizedRerootCompoundRule5Readings .R
      [{ prior := { reference? := some RS.R, rule4bKey := k4bR, rule4cKey := k4cR },
         commonR := input.rule5LiftKey (RS.R == RS.R) k4cR,
         commonS := input.rule5LiftKey (RS.S == RS.R) k4cR },
       { prior := { reference? := some RS.S, rule4bKey := k4bS, rule4cKey := k4cS },
         commonR := input.rule5LiftKey (RS.R == RS.S) k4cS,
         commonS := input.rule5LiftKey (RS.S == RS.S) k4cS }]
      [{ prior := compoundUppercaseRule4bcReading input
           { reference? := some RS.S, rule4bKey := k4bS, rule4cKey := k4cS },
         commonR := reflectLocalizedRerootCumulativeRule45Key input
           (input.rule5LiftKey (RS.S == RS.S) k4cS),
         commonS := reflectLocalizedRerootCumulativeRule45Key input
           (input.rule5LiftKey (RS.R == RS.S) k4cS) },
       { prior := compoundUppercaseRule4bcReading input
           { reference? := some RS.R, rule4bKey := k4bR, rule4cKey := k4cR },
         commonR := reflectLocalizedRerootCumulativeRule45Key input
           (input.rule5LiftKey (RS.S == RS.R) k4cR),
         commonS := reflectLocalizedRerootCumulativeRule45Key input
           (input.rule5LiftKey (RS.R == RS.R) k4cR) }] = Ordering.eq := by
    have hRR : (RS.R == RS.R) = true := rfl
    have hSS : (RS.S == RS.S) = true := rfl
    have hRS : (RS.R == RS.S) = false := rfl
    have hSR : (RS.S == RS.R) = false := rfl
    unfold compareLocalizedRerootCompoundRule5Readings
    simp only [List.compareLex, Ordering.byKey, localizedRerootRule5Descriptor,
      reflectLocalizedRerootCumulativeRule45Key, rule5LiftKey, tableEq, hRR, hSS, hRS, hSR,
      compareSparseLayers_refl]
  rw [cmpR]

/-- Every reading list built by the compiler has the length of its alternative list. -/
private theorem buildLocalizedRerootRule4bcReadings?_length
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∀ (alternatives : List (Option RS)) (readings : List input.LocalizedRerootRule4bcReading),
      input.buildLocalizedRerootRule4bcReadings? target view fuel cursor alternatives =
        some readings → readings.length = alternatives.length
  | [], readings, h => by
      simp only [buildLocalizedRerootRule4bcReadings?, Option.some.injEq] at h
      subst h; rfl
  | alternative :: alternatives, readings, h => by
      simp only [buildLocalizedRerootRule4bcReadings?] at h
      cases hr : input.buildLocalizedRerootRule4bcReading? target view fuel cursor alternative with
      | none => simp [hr] at h
      | some reading =>
          cases hrs : input.buildLocalizedRerootRule4bcReadings? target view fuel cursor
              alternatives with
          | none => simp [hr, hrs] at h
          | some rest =>
              simp only [hr, hrs, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
              subst h
              simp [buildLocalizedRerootRule4bcReadings?_length target view fuel cursor alternatives
                rest hrs]

private theorem buildLocalizedRerootRule5Readings?_length
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∀ (priors : List input.LocalizedRerootRule4bcReading)
      (readings : List input.LocalizedRerootRule5Reading),
      input.buildLocalizedRerootRule5Readings? target view fuel cursor priors = some readings →
        readings.length = priors.length
  | [], readings, h => by
      simp only [buildLocalizedRerootRule5Readings?, Option.some.injEq] at h
      subst h; rfl
  | prior :: priors, readings, h => by
      simp only [buildLocalizedRerootRule5Readings?] at h
      cases hr : input.buildLocalizedRerootRule5Reading? target view fuel cursor prior with
      | none => simp [hr] at h
      | some reading =>
          cases hrs : input.buildLocalizedRerootRule5Readings? target view fuel cursor priors with
          | none => simp [hr, hrs] at h
          | some rest =>
              simp only [hr, hrs, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
              subst h
              simp [buildLocalizedRerootRule5Readings?_length target view fuel cursor priors rest hrs]


/-- The alternative list of a built compound key has at most two entries, and exactly two only
for the selection `[R, S]`. -/
theorem built_prior_shape
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootCompoundRule4bcKey)
    (computed : input.buildLocalizedRerootCompoundRule4bcKey? target view fuel cursor = some prior) :
    prior.readings.length ≤ 2 ∧
      (prior.readings.length = 2 → prior.references = [RS.R, RS.S]) := by
  unfold buildLocalizedRerootCompoundRule4bcKey? at computed
  cases h4a : input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view fuel cursor with
  | none => simp [h4a] at computed
  | some rule4aKey =>
  simp only [h4a, Option.bind_eq_bind, Option.bind_some] at computed
  cases hreads : input.buildLocalizedRerootRule4bcReadings? target view fuel cursor
      (localizedRule4bcReferenceAlternatives
        (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) with
  | none => simp [hreads] at computed
  | some reads =>
  simp only [hreads, Option.bind_some, Option.some.injEq] at computed
  subst computed
  have hlen := input.buildLocalizedRerootRule4bcReadings?_length target view fuel cursor _ _ hreads
  simp only
  unfold localizedRule4bReferencesFromRankedLabels at hlen ⊢
  generalize localizedFirstChiralRankPopulation rule4aKey.rankedLabels = population at hlen ⊢
  unfold localizedRule4bReferencesFromPopulation at hlen ⊢
  dsimp only at hlen ⊢
  split_ifs at hlen ⊢ <;> simp_all [localizedRule4bcReferenceAlternatives]

/-- **An arm never decides an uppercase letter against its own mirror image.**  For every built
compound key, the ordered through-Rule-5 comparison against the ordered key-level mirror either
ties completely or is a Rule-5 decision flagged enantiomorphic. -/
theorem built_mirror_eq_or_pseudo
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule45Key)
    (computed : input.buildLocalizedRerootCompoundRule45Key? target view fuel cursor = some key) :
    (input.compareLocalizedRerootCompoundThroughRule5 (input.outcomeOrdered45 key)
        (input.outcomeOrdered45 (compoundUppercaseCompoundRule45Key input key))).ordering = .eq ∨
      (input.compareLocalizedRerootCompoundThroughRule5 (input.outcomeOrdered45 key)
        (input.outcomeOrdered45 (compoundUppercaseCompoundRule45Key input key))).pseudo = true := by
  have computed' := computed
  unfold buildLocalizedRerootCompoundRule45Key? at computed'
  cases hprior : input.buildLocalizedRerootCompoundRule4bcKey? target view fuel cursor with
  | none => simp [hprior] at computed'
  | some prior =>
  cases hread : input.buildLocalizedRerootRule5Readings? target view fuel cursor prior.readings with
  | none => simp [hprior, hread] at computed'
  | some readings =>
  simp only [hprior, hread, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at computed'
  subst computed'
  obtain ⟨priorBounded, twoRefs⟩ := input.built_prior_shape target view fuel cursor prior hprior
  have readLen := input.buildLocalizedRerootRule5Readings?_length target view fuel cursor _ _ hread
  by_cases strict : ∀ a b, readings = [a, b] →
      input.compareRule4bcReadingsComplete a.prior b.prior ≠ .eq
  · have h := input.outcomeOrdered45_reflect_pseudo ⟨prior, readings⟩ priorBounded
      (by simp only; omega) strict
    simp only at h
    by_cases heq : (input.compareLocalizedRerootCompoundThroughRule5 (input.outcomeOrdered45 ⟨prior, readings⟩)
        (input.outcomeOrdered45 (compoundUppercaseCompoundRule45Key input ⟨prior, readings⟩))).ordering = .eq
    · exact Or.inl heq
    · right
      rw [h]
      exact decide_eq_true heq
  · left
    push_neg at strict
    obtain ⟨a, b, hab, htie⟩ := strict
    have two : prior.references = [RS.R, RS.S] := twoRefs (by rw [← readLen, hab]; rfl)
    have priorsEq : prior.readings = [a.prior, b.prior] := by
      rw [← input.buildLocalizedRerootRule5Readings?_map_prior target view fuel cursor _ _ hread, hab]
      rfl
    have tie : ∀ x y, prior.readings = [x, y] → input.compareRule4bcReadingsComplete x y = .eq := by
      intro x y hxy
      rw [priorsEq] at hxy
      cases hxy
      exact htie
    rw [input.fullTie_throughRule5_mirror_eq target view fuel cursor ⟨prior, readings⟩ computed two tie]

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule5Lift_priority
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45Key?_rule5
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.fullTie_throughRule5_mirror_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.built_mirror_eq_or_pseudo
