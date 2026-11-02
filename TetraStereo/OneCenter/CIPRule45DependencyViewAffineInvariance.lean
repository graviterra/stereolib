import TetraStereo.OneCenter.CIPRule3CanonicalBuilderAffineInvariance

/-!
# Coordinate naturality of the occurrence-local Rules-4a--5 compiler

Coordinate transport preserves the exact finite occurrence carrier and therefore induces an
inverse on its occurrence subtype. This module uses that inverse to transport a proof-restricted
dependency view. It then proves that strict-depth label reads, cumulative sibling sorting,
hierarchy-equivalence ranks, Rule-4b reference selection, compound Rule-4b/4c alternatives, and
the paired Rule-5 readings all commute with an arbitrary coordinate map.

Unlike Rule 3, this layer uses no geometric orientation, so invertibility is unnecessary: the
theorems require only the canonical transport of the same dependency state.
-/

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

private theorem exists_unmappedLocalizedCIPOccurrenceFrame
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (mapPoint : CartesianPoint3 → CartesianPoint3)
    (occurrence : (input.mapSpatialPoints mapPoint).LocalizedCIPOccurrence fuel) :
    ∃ frame ∈ input.localizedOccurrences fuel,
      frame.mapSpatialPoints mapPoint = occurrence.1 := by
  have mappedPresent : occurrence.1 ∈
      (input.localizedOccurrences fuel).map
        (fun frame => frame.mapSpatialPoints mapPoint) := by
    simpa only [localizedOccurrences_mapSpatialPoints] using occurrence.2
  exact List.mem_map.mp mappedPresent

private theorem LocalizedCIPOccurrenceFrame.mapSpatialPoints_injective
    {input : CertifiedLocalizedCIPInput}
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    Function.Injective (fun frame : input.LocalizedCIPOccurrenceFrame =>
      frame.mapSpatialPoints mapPoint) := by
  intro left right equal
  cases left
  cases right
  simp only [LocalizedCIPOccurrenceFrame.mapSpatialPoints] at equal
  simp_all

noncomputable def LocalizedCIPOccurrence.unmapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (mapPoint : CartesianPoint3 → CartesianPoint3)
    (occurrence : (input.mapSpatialPoints mapPoint).LocalizedCIPOccurrence fuel) :
    input.LocalizedCIPOccurrence fuel :=
  ⟨Classical.choose (exists_unmappedLocalizedCIPOccurrenceFrame mapPoint occurrence),
    (Classical.choose_spec
      (exists_unmappedLocalizedCIPOccurrenceFrame mapPoint occurrence)).1⟩

@[simp] theorem LocalizedCIPOccurrence.unmap_mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (occurrence.mapSpatialPoints mapPoint).unmapSpatialPoints mapPoint = occurrence := by
  apply Subtype.ext
  exact LocalizedCIPOccurrenceFrame.mapSpatialPoints_injective mapPoint
    (Classical.choose_spec
    (exists_unmappedLocalizedCIPOccurrenceFrame mapPoint
      (occurrence.mapSpatialPoints mapPoint))).2

@[simp] theorem LocalizedCIPOccurrence.map_unmapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (mapPoint : CartesianPoint3 → CartesianPoint3)
    (occurrence : (input.mapSpatialPoints mapPoint).LocalizedCIPOccurrence fuel) :
    (occurrence.unmapSpatialPoints mapPoint).mapSpatialPoints mapPoint = occurrence := by
  apply Subtype.ext
  exact (Classical.choose_spec
    (exists_unmappedLocalizedCIPOccurrenceFrame mapPoint occurrence)).2

@[simp] theorem localizedDepthDependency_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    {fuel : Nat} (source target : input.LocalizedCIPOccurrence fuel) :
    (input.mapSpatialPoints mapPoint).LocalizedDepthDependency
        (source.mapSpatialPoints mapPoint) (target.mapSpatialPoints mapPoint) ↔
      input.LocalizedDepthDependency source target := by
  rfl

@[simp] theorem localizedDepthDependency_unmapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    {fuel : Nat}
    (source target : (input.mapSpatialPoints mapPoint).LocalizedCIPOccurrence fuel) :
    input.LocalizedDepthDependency (source.unmapSpatialPoints mapPoint)
        (target.unmapSpatialPoints mapPoint) ↔
      (input.mapSpatialPoints mapPoint).LocalizedDepthDependency source target := by
  unfold LocalizedDepthDependency
  have sourceEqual := congrArg Subtype.val
    (LocalizedCIPOccurrence.map_unmapSpatialPoints mapPoint source)
  have targetEqual := congrArg Subtype.val
    (LocalizedCIPOccurrence.map_unmapSpatialPoints mapPoint target)
  simp only [LocalizedCIPOccurrence.mapSpatialPoints,
    LocalizedCIPOccurrenceFrame.mapSpatialPoints] at sourceEqual targetEqual
  rw [← sourceEqual, ← targetEqual]

noncomputable def LocalizedDependencyView.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (view : input.LocalizedDependencyView target)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedDependencyView
      (target.mapSpatialPoints mapPoint) :=
  fun source dependency =>
    view (source.unmapSpatialPoints mapPoint)
      (by
        have unmapDependency :=
          (localizedDepthDependency_unmapSpatialPoints input mapPoint source
            (target.mapSpatialPoints mapPoint)).mpr dependency
        simpa using unmapDependency)

@[simp] theorem LocalizedDependencyView.mapSpatialPoints_apply
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (view : input.LocalizedDependencyView target)
    (mapPoint : CartesianPoint3 → CartesianPoint3)
    (source : input.LocalizedCIPOccurrence fuel)
    (dependency : input.LocalizedDepthDependency source target)
    (mappedDependency : (input.mapSpatialPoints mapPoint).LocalizedDepthDependency
      (source.mapSpatialPoints mapPoint) (target.mapSpatialPoints mapPoint)) :
    view.mapSpatialPoints mapPoint (source.mapSpatialPoints mapPoint) mappedDependency =
      view source dependency := by
  unfold LocalizedDependencyView.mapSpatialPoints
  congr
  exact LocalizedCIPOccurrence.unmap_mapSpatialPoints source mapPoint

@[simp] theorem localizedDependencyLabel_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedDependencyLabel
        (target.mapSpatialPoints mapPoint) (view.mapSpatialPoints mapPoint)
        (cursor.mapSpatialPoints mapPoint) =
      input.localizedDependencyLabel target view cursor := by
  unfold localizedDependencyLabel
  split
  · rename_i mappedDependency
    have dependency : input.LocalizedDepthDependency cursor.occurrence target :=
      (localizedDepthDependency_mapSpatialPoints input mapPoint _ _).mp mappedDependency
    simp only [dif_pos dependency]
    exact LocalizedDependencyView.mapSpatialPoints_apply
      view mapPoint cursor.occurrence dependency mappedDependency
  · rename_i notMappedDependency
    have notDependency : ¬ input.LocalizedDepthDependency cursor.occurrence target := by
      intro dependency
      exact notMappedDependency
        ((localizedDepthDependency_mapSpatialPoints input mapPoint _ _).mpr dependency)
    simp [notDependency]

@[simp] theorem compareLocalizedRerootCumulativeRule45Keys_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (left right : input.LocalizedRerootCumulativeRule45Key) :
    (input.mapSpatialPoints mapPoint).compareLocalizedRerootCumulativeRule45Keys
        (left.mapSpatialPoints mapPoint) (right.mapSpatialPoints mapPoint) =
      input.compareLocalizedRerootCumulativeRule45Keys left right := by
  rfl

@[simp] theorem insertLocalizedRerootCumulativeRule45Key_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    ∀ keys : List input.LocalizedRerootCumulativeRule45Key,
    (input.mapSpatialPoints mapPoint).insertLocalizedRerootCumulativeRule45Key
        (key.mapSpatialPoints mapPoint)
        (keys.map fun child => child.mapSpatialPoints mapPoint) =
      (input.insertLocalizedRerootCumulativeRule45Key key keys).map
        (fun child => child.mapSpatialPoints mapPoint)
  | [] => rfl
  | head :: tail => by
      simp only [List.map_cons]
      unfold insertLocalizedRerootCumulativeRule45Key
      rw [compareLocalizedRerootCumulativeRule45Keys_mapSpatialPoints]
      cases input.compareLocalizedRerootCumulativeRule45Keys key head <;>
        simp [insertLocalizedRerootCumulativeRule45Key_mapSpatialPoints]

@[simp] theorem sortLocalizedRerootCumulativeRule45Keys_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3) :
    ∀ keys : List input.LocalizedRerootCumulativeRule45Key,
    (input.mapSpatialPoints mapPoint).sortLocalizedRerootCumulativeRule45Keys
        (keys.map fun child => child.mapSpatialPoints mapPoint) =
      (input.sortLocalizedRerootCumulativeRule45Keys keys).map
        (fun child => child.mapSpatialPoints mapPoint)
  | [] => rfl
  | key :: keys => by
      simp only [List.map_cons]
      unfold sortLocalizedRerootCumulativeRule45Keys
      rw [sortLocalizedRerootCumulativeRule45Keys_mapSpatialPoints,
        insertLocalizedRerootCumulativeRule45Key_mapSpatialPoints]

private theorem cumulativeFieldLayerCount_mapSpatialPoints
    {α β : Type*} (input : CertifiedLocalizedCIPInput)
    (mapPoint : CartesianPoint3 → CartesianPoint3)
    (field : input.LocalizedRerootCumulativeRule45Key → List α)
    (mappedField :
      (input.mapSpatialPoints mapPoint).LocalizedRerootCumulativeRule45Key → List β)
    (lengthNatural : ∀ key, (mappedField (key.mapSpatialPoints mapPoint)).length =
      (field key).length) :
    ∀ children : List input.LocalizedRerootCumulativeRule45Key,
    (children.map fun child => child.mapSpatialPoints mapPoint).foldl
        (fun longest child => max longest (mappedField child).length) 0 =
      children.foldl (fun longest child => max longest (field child).length) 0
  | [] => rfl
  | child :: children => by
      simp only [List.map_cons, List.foldl_cons, lengthNatural]
      generalize initial : (field child).length = accumulator
      clear initial child
      induction children generalizing accumulator with
      | nil => rfl
      | cons next tail ih =>
          simp only [List.map_cons, List.foldl_cons, lengthNatural]
          exact ih _

@[simp] theorem localizedRerootDescriptorChildLayerCount_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    (input.mapSpatialPoints mapPoint).localizedRerootDescriptorChildLayerCount
        (children.map fun child => child.mapSpatialPoints mapPoint) =
      input.localizedRerootDescriptorChildLayerCount children := by
  unfold localizedRerootDescriptorChildLayerCount
  exact cumulativeFieldLayerCount_mapSpatialPoints input mapPoint
    (fun key => key.descriptor) (fun key => key.descriptor) (fun _ => rfl) children

@[simp] theorem localizedRerootLabelChildLayerCount_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    (input.mapSpatialPoints mapPoint).localizedRerootLabelChildLayerCount
        (children.map fun child => child.mapSpatialPoints mapPoint) =
      input.localizedRerootLabelChildLayerCount children := by
  unfold localizedRerootLabelChildLayerCount
  exact cumulativeFieldLayerCount_mapSpatialPoints input mapPoint
    (fun key => key.labels) (fun key => key.labels) (fun _ => rfl) children

@[simp] theorem localizedRerootRankedLabelChildLayerCount_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    (input.mapSpatialPoints mapPoint).localizedRerootRankedLabelChildLayerCount
        (children.map fun child => child.mapSpatialPoints mapPoint) =
      input.localizedRerootRankedLabelChildLayerCount children := by
  unfold localizedRerootRankedLabelChildLayerCount
  exact cumulativeFieldLayerCount_mapSpatialPoints input mapPoint
    (fun key => key.rankedLabels) (fun key => key.rankedLabels) (fun _ => rfl) children

@[simp] theorem mergeLocalizedRerootDescriptorChildren_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    (input.mapSpatialPoints mapPoint).mergeLocalizedRerootDescriptorChildren
        (children.map fun child => child.mapSpatialPoints mapPoint) =
      input.mergeLocalizedRerootDescriptorChildren children := by
  unfold mergeLocalizedRerootDescriptorChildren
  rw [localizedRerootDescriptorChildLayerCount_mapSpatialPoints]
  apply List.map_congr_left
  intro depth depthPresent
  rw [List.zipIdx_map, List.flatMap_map]
  apply List.flatMap_congr
  intro child childPresent
  cases child
  rfl

@[simp] theorem mergeLocalizedRerootLabelChildren_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    (input.mapSpatialPoints mapPoint).mergeLocalizedRerootLabelChildren
        (children.map fun child => child.mapSpatialPoints mapPoint) =
      input.mergeLocalizedRerootLabelChildren children := by
  unfold mergeLocalizedRerootLabelChildren
  rw [localizedRerootLabelChildLayerCount_mapSpatialPoints]
  apply List.map_congr_left
  intro depth depthPresent
  rw [List.zipIdx_map, List.flatMap_map]
  apply List.flatMap_congr
  intro child childPresent
  cases child
  rfl

@[simp] theorem localizedRerootRankedChildTail_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (previous : input.LocalizedRerootCumulativeRule45Key) (rank : Nat) :
    ∀ children : List input.LocalizedRerootCumulativeRule45Key,
    (input.mapSpatialPoints mapPoint).localizedRerootRankedChildTail
        (previous.mapSpatialPoints mapPoint) rank
        (children.map fun child => child.mapSpatialPoints mapPoint) =
      (input.localizedRerootRankedChildTail previous rank children).map
        (fun child => (child.1.mapSpatialPoints mapPoint, child.2))
  | [] => rfl
  | child :: children => by
      simp only [List.map_cons]
      unfold localizedRerootRankedChildTail
      rw [compareLocalizedRerootCumulativeRule45Keys_mapSpatialPoints]
      split <;> simp [localizedRerootRankedChildTail_mapSpatialPoints]

@[simp] theorem localizedRerootRankedChildren_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3) :
    ∀ children : List input.LocalizedRerootCumulativeRule45Key,
    (input.mapSpatialPoints mapPoint).localizedRerootRankedChildren
        (children.map fun child => child.mapSpatialPoints mapPoint) =
      (input.localizedRerootRankedChildren children).map
        (fun child => (child.1.mapSpatialPoints mapPoint, child.2))
  | [] => rfl
  | child :: children => by
      simp only [List.map_cons, localizedRerootRankedChildren]
      rw [localizedRerootRankedChildTail_mapSpatialPoints]

@[simp] theorem mergeLocalizedRerootRankedLabelChildren_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    (input.mapSpatialPoints mapPoint).mergeLocalizedRerootRankedLabelChildren
        (children.map fun child => child.mapSpatialPoints mapPoint) =
      input.mergeLocalizedRerootRankedLabelChildren children := by
  unfold mergeLocalizedRerootRankedLabelChildren
  rw [localizedRerootRankedLabelChildLayerCount_mapSpatialPoints,
    localizedRerootRankedChildren_mapSpatialPoints]
  apply List.map_congr_left
  intro depth depthPresent
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro child childPresent
  cases child
  rfl

theorem buildLocalizedRerootCumulativeRule45Key?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
    (input.mapSpatialPoints mapPoint).buildLocalizedRerootCumulativeRule45Key?
        stage (target.mapSpatialPoints mapPoint) (view.mapSpatialPoints mapPoint)
        fuel (cursor.mapSpatialPoints mapPoint) =
      (input.buildLocalizedRerootCumulativeRule45Key?
        stage target view fuel cursor).map
          (fun key => key.mapSpatialPoints mapPoint)
  | 0, cursor => by
      unfold buildLocalizedRerootCumulativeRule45Key?
      rw [localizedRerootChildren?_mapSpatialPoints]
      rw [localizedDependencyLabel_mapSpatialPoints]
      cases childrenEq : input.localizedRerootChildren? cursor with
      | none => rfl
      | some children =>
          have nodeEq :
              (cursor.mapSpatialPoints mapPoint).occurrence.1.node =
                cursor.occurrence.1.node := rfl
          rw [nodeEq]
          by_cases terminal : children = []
          · simp [terminal, moleculeGraph_mapSpatialPoints,
              LocalizedRerootCumulativeRule45Key.mapSpatialPoints]
          · simp [terminal]
  | fuel + 1, cursor => by
      unfold buildLocalizedRerootCumulativeRule45Key?
      rw [localizedRerootChildren?_mapSpatialPoints]
      rw [localizedDependencyLabel_mapSpatialPoints]
      cases childrenEq : input.localizedRerootChildren? cursor with
      | none => rfl
      | some children =>
          have nodeEq :
              (cursor.mapSpatialPoints mapPoint).occurrence.1.node =
                cursor.occurrence.1.node := rfl
          rw [nodeEq]
          by_cases terminal : children = []
          · simp [terminal, moleculeGraph_mapSpatialPoints,
              LocalizedRerootCumulativeRule45Key.mapSpatialPoints]
          · simp [terminal]
            have mapMNatural :
                children.mapM
                    ((input.mapSpatialPoints mapPoint).buildLocalizedRerootCumulativeRule45Key?
                      stage (target.mapSpatialPoints mapPoint)
                        (view.mapSpatialPoints mapPoint) fuel ∘
                      fun child => child.mapSpatialPoints mapPoint) =
                  (children.mapM
                    (input.buildLocalizedRerootCumulativeRule45Key?
                      stage target view fuel)).map
                    (fun keys => keys.map fun key => key.mapSpatialPoints mapPoint) :=
              listMapM_map_of_natural
                (fun child => child.mapSpatialPoints mapPoint)
                (fun key => key.mapSpatialPoints mapPoint)
                (input.buildLocalizedRerootCumulativeRule45Key? stage target view fuel)
                ((input.mapSpatialPoints mapPoint).buildLocalizedRerootCumulativeRule45Key?
                  stage (target.mapSpatialPoints mapPoint)
                    (view.mapSpatialPoints mapPoint) fuel)
                (fun child => buildLocalizedRerootCumulativeRule45Key?_mapSpatialPoints
                  input stage target view mapPoint fuel child)
                children
            rw [mapMNatural]
            cases childKeysEq : children.mapM
                (input.buildLocalizedRerootCumulativeRule45Key?
                  stage target view fuel) with
            | none => rfl
            | some childKeys =>
                simp only [Option.map_some, Option.bind_some]
                rw [sortLocalizedRerootCumulativeRule45Keys_mapSpatialPoints]
                rw [mergeLocalizedRerootDescriptorChildren_mapSpatialPoints,
                  mergeLocalizedRerootLabelChildren_mapSpatialPoints,
                  mergeLocalizedRerootRankedLabelChildren_mapSpatialPoints]
                simp only [LocalizedRerootCumulativeRule45Key.mapSpatialPoints,
                  List.map_map]
                rfl

theorem buildLocalizedRerootRule4bcReading?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3)
    (reference : Option RS) :
    (input.mapSpatialPoints mapPoint).buildLocalizedRerootRule4bcReading?
        (target.mapSpatialPoints mapPoint) (view.mapSpatialPoints mapPoint)
        fuel (cursor.mapSpatialPoints mapPoint) reference =
      (input.buildLocalizedRerootRule4bcReading?
        target view fuel cursor reference).map
          (fun reading => reading.mapSpatialPoints mapPoint) := by
  cases reference with
  | none =>
      simp only [buildLocalizedRerootRule4bcReading?]
      rw [buildLocalizedRerootCumulativeRule45Key?_mapSpatialPoints
        input .rule4a target view mapPoint fuel cursor]
      cases firstEq : input.buildLocalizedRerootCumulativeRule45Key?
          .rule4a target view fuel cursor with
      | none => rfl
      | some first =>
          simp only [Option.map_some]
          rw [buildLocalizedRerootCumulativeRule45Key?_mapSpatialPoints
            input .rule4cNoReference target view mapPoint fuel cursor]
          cases secondEq : input.buildLocalizedRerootCumulativeRule45Key?
              .rule4cNoReference target view fuel cursor <;> rfl
  | some reference =>
      simp only [buildLocalizedRerootRule4bcReading?]
      rw [buildLocalizedRerootCumulativeRule45Key?_mapSpatialPoints
        input (.rule4b reference) target view mapPoint fuel cursor]
      cases firstEq : input.buildLocalizedRerootCumulativeRule45Key?
          (.rule4b reference) target view fuel cursor with
      | none => rfl
      | some first =>
          simp only [Option.map_some]
          rw [buildLocalizedRerootCumulativeRule45Key?_mapSpatialPoints
            input (.rule4c reference) target view mapPoint fuel cursor]
          cases secondEq : input.buildLocalizedRerootCumulativeRule45Key?
              (.rule4c reference) target view fuel cursor <;> rfl

theorem buildLocalizedRerootRule4bcReadings?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    ∀ references : List (Option RS),
    (input.mapSpatialPoints mapPoint).buildLocalizedRerootRule4bcReadings?
        (target.mapSpatialPoints mapPoint) (view.mapSpatialPoints mapPoint)
        fuel (cursor.mapSpatialPoints mapPoint) references =
      (input.buildLocalizedRerootRule4bcReadings?
        target view fuel cursor references).map
          (fun readings => readings.map fun reading => reading.mapSpatialPoints mapPoint)
  | [] => rfl
  | reference :: references => by
      unfold buildLocalizedRerootRule4bcReadings?
      rw [buildLocalizedRerootRule4bcReading?_mapSpatialPoints]
      rw [buildLocalizedRerootRule4bcReadings?_mapSpatialPoints]
      cases headEq : input.buildLocalizedRerootRule4bcReading?
          target view fuel cursor reference <;> simp
      cases tailEq : input.buildLocalizedRerootRule4bcReadings?
          target view fuel cursor references <;> rfl

theorem buildLocalizedRerootCompoundRule4bcKey?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).buildLocalizedRerootCompoundRule4bcKey?
        (target.mapSpatialPoints mapPoint) (view.mapSpatialPoints mapPoint)
        fuel (cursor.mapSpatialPoints mapPoint) =
      (input.buildLocalizedRerootCompoundRule4bcKey?
        target view fuel cursor).map
          (fun key => key.mapSpatialPoints mapPoint) := by
  unfold buildLocalizedRerootCompoundRule4bcKey?
  rw [buildLocalizedRerootCumulativeRule45Key?_mapSpatialPoints]
  change
    (((fun key : input.LocalizedRerootCumulativeRule45Key =>
        key.mapSpatialPoints mapPoint) <$>
      input.buildLocalizedRerootCumulativeRule45Key?
        .rule4a target view fuel cursor) >>= _) =
      ((fun key : input.LocalizedRerootCompoundRule4bcKey =>
        key.mapSpatialPoints mapPoint) <$>
      (input.buildLocalizedRerootCumulativeRule45Key?
        .rule4a target view fuel cursor >>= _))
  rw [bind_map_left, map_bind]
  apply congrArg (Option.bind
    (input.buildLocalizedRerootCumulativeRule45Key?
      .rule4a target view fuel cursor))
  funext rule4aKey
  simp only [LocalizedRerootCumulativeRule45Key.mapSpatialPoints]
  rw [buildLocalizedRerootRule4bcReadings?_mapSpatialPoints]
  cases input.buildLocalizedRerootRule4bcReadings? target view fuel cursor
      (localizedRule4bcReferenceAlternatives
        (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) <;> rfl

theorem buildLocalizedRerootRule5Reading?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).buildLocalizedRerootRule5Reading?
        (target.mapSpatialPoints mapPoint) (view.mapSpatialPoints mapPoint)
        fuel (cursor.mapSpatialPoints mapPoint) (prior.mapSpatialPoints mapPoint) =
      (input.buildLocalizedRerootRule5Reading?
        target view fuel cursor prior).map
          (fun reading => reading.mapSpatialPoints mapPoint) := by
  unfold buildLocalizedRerootRule5Reading?
  simp only [LocalizedRerootRule4bcReading.mapSpatialPoints]
  rw [buildLocalizedRerootCumulativeRule45Key?_mapSpatialPoints
    input (localizedRule5StageFor prior.reference? .R)
      target view mapPoint fuel cursor]
  cases firstEq : input.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor prior.reference? .R) target view fuel cursor with
  | none => rfl
  | some first =>
      simp only [Option.map_some]
      rw [buildLocalizedRerootCumulativeRule45Key?_mapSpatialPoints
        input (localizedRule5StageFor prior.reference? .S)
          target view mapPoint fuel cursor]
      cases secondEq : input.buildLocalizedRerootCumulativeRule45Key?
          (localizedRule5StageFor prior.reference? .S) target view fuel cursor <;> rfl

theorem buildLocalizedRerootRule5Readings?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    ∀ priors : List input.LocalizedRerootRule4bcReading,
    (input.mapSpatialPoints mapPoint).buildLocalizedRerootRule5Readings?
        (target.mapSpatialPoints mapPoint) (view.mapSpatialPoints mapPoint)
        fuel (cursor.mapSpatialPoints mapPoint)
        (priors.map fun prior => prior.mapSpatialPoints mapPoint) =
      (input.buildLocalizedRerootRule5Readings?
        target view fuel cursor priors).map
          (fun readings => readings.map fun reading => reading.mapSpatialPoints mapPoint)
  | [] => rfl
  | prior :: priors => by
      simp only [List.map_cons]
      unfold buildLocalizedRerootRule5Readings?
      rw [buildLocalizedRerootRule5Reading?_mapSpatialPoints]
      rw [buildLocalizedRerootRule5Readings?_mapSpatialPoints]
      cases headEq : input.buildLocalizedRerootRule5Reading?
          target view fuel cursor prior <;> simp
      cases tailEq : input.buildLocalizedRerootRule5Readings?
          target view fuel cursor priors <;> rfl

theorem buildLocalizedRerootCompoundRule45Key?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).buildLocalizedRerootCompoundRule45Key?
        (target.mapSpatialPoints mapPoint) (view.mapSpatialPoints mapPoint)
        fuel (cursor.mapSpatialPoints mapPoint) =
      (input.buildLocalizedRerootCompoundRule45Key?
        target view fuel cursor).map
          (fun key => key.mapSpatialPoints mapPoint) := by
  unfold buildLocalizedRerootCompoundRule45Key?
  rw [buildLocalizedRerootCompoundRule4bcKey?_mapSpatialPoints]
  change
    (((fun key : input.LocalizedRerootCompoundRule4bcKey =>
        key.mapSpatialPoints mapPoint) <$>
      input.buildLocalizedRerootCompoundRule4bcKey? target view fuel cursor) >>= _) =
      ((fun key : input.LocalizedRerootCompoundRule45Key =>
        key.mapSpatialPoints mapPoint) <$>
      (input.buildLocalizedRerootCompoundRule4bcKey? target view fuel cursor >>= _))
  rw [bind_map_left, map_bind]
  apply congrArg (Option.bind
    (input.buildLocalizedRerootCompoundRule4bcKey? target view fuel cursor))
  funext prior
  simp only [LocalizedRerootCompoundRule4bcKey.mapSpatialPoints]
  rw [buildLocalizedRerootRule5Readings?_mapSpatialPoints]
  cases input.buildLocalizedRerootRule5Readings?
      target view fuel cursor prior.readings <;> rfl

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
