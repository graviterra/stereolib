import TetraStereo.OneCenter.CIPRule3DescriptorKeyAffineInvariance

set_option autoImplicit false

/-!
# Affine naturality of the recursive occurrence-local Rule-3 key compiler

This module proves that changing only the exact spatial coordinate frame transports the finite
occurrence carrier, reroot zipper, bottom-up Rules-1a--3 sorting, sparse observation layers, and
the complete recursive key compiler.  The main theorem covers every success and refusal branch
under an arbitrary invertible rational affine map, including shears and reflections.
-/

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

def LocalizedCIPOccurrenceFrame.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput}
    (frame : input.LocalizedCIPOccurrenceFrame)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedCIPOccurrenceFrame :=
  { root := frame.root
    address := frame.address
    node := frame.node
    remaining := frame.remaining }

@[simp] theorem localizedOccurrenceSubtree_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (root : input.Atom) (fuel : Nat) (path : List Nat)
    (node : OfficialCIPNode input.Atom) :
    (input.mapSpatialPoints mapPoint).localizedOccurrenceSubtree root fuel path node =
      (input.localizedOccurrenceSubtree root fuel path node).map
        (fun frame => frame.mapSpatialPoints mapPoint) := by
  induction fuel generalizing path node with
  | zero => rfl
  | succ fuel ih =>
      simp only [localizedOccurrenceSubtree, List.map_cons]
      rw [executableOfficialCIPChildren_mapSpatialPoints]
      simp only [List.map_flatMap]
      apply congrArg (List.cons _)
      apply List.flatMap_congr
      intro child childPresent
      exact ih _ _

@[simp] theorem localizedOccurrencesAtAtom_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (fuel : Nat) (atom : input.Atom) :
    (input.mapSpatialPoints mapPoint).localizedOccurrencesAtAtom fuel atom =
      (input.localizedOccurrencesAtAtom fuel atom).map
        (fun frame => frame.mapSpatialPoints mapPoint) := by
  unfold localizedOccurrencesAtAtom
  exact localizedOccurrenceSubtree_mapSpatialPoints input mapPoint atom _ _ _

@[simp] theorem localizedOccurrences_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (fuel : Nat) :
    (input.mapSpatialPoints mapPoint).localizedOccurrences fuel =
      (input.localizedOccurrences fuel).map
        (fun frame => frame.mapSpatialPoints mapPoint) := by
  unfold localizedOccurrences
  change
    ((List.finRange input.certified.input.molecule.atomCount).flatMap
      ((input.mapSpatialPoints mapPoint).localizedOccurrencesAtAtom fuel)).dedup = _
  rw [← List.dedup_map_of_injective]
  · apply congrArg List.dedup
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro atom atomPresent
    exact localizedOccurrencesAtAtom_mapSpatialPoints input mapPoint fuel atom
  · intro left right equal
    cases left
    cases right
    simp only [LocalizedCIPOccurrenceFrame.mapSpatialPoints] at equal
    simp_all

def LocalizedCIPOccurrence.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedCIPOccurrence fuel :=
  ⟨occurrence.1.mapSpatialPoints mapPoint, by
    rw [localizedOccurrences_mapSpatialPoints]
    exact List.mem_map.mpr ⟨occurrence.1, occurrence.2, rfl⟩⟩

def LocalizedRerootCursor.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRerootCursor fuel :=
  { occurrence := cursor.occurrence.mapSpatialPoints mapPoint
    previous? := cursor.previous?.map (fun previous => previous.mapSpatialPoints mapPoint) }

@[simp] theorem localizedCarrierParentFrames_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    {fuel : Nat} (frame : input.LocalizedCIPOccurrenceFrame) :
    (input.mapSpatialPoints mapPoint).localizedCarrierParentFrames
        (fuel := fuel) (frame.mapSpatialPoints mapPoint) =
      (input.localizedCarrierParentFrames (fuel := fuel) frame).map
        (fun parent => parent.mapSpatialPoints mapPoint) := by
  unfold localizedCarrierParentFrames
  rw [localizedOccurrences_mapSpatialPoints, List.filter_map]
  have predicateEq :
      ((fun candidate : (input.mapSpatialPoints mapPoint).LocalizedCIPOccurrenceFrame =>
          candidate.root == (frame.mapSpatialPoints mapPoint).root &&
            candidate.address.length + 1 == (frame.mapSpatialPoints mapPoint).address.length &&
            candidate.address == (frame.mapSpatialPoints mapPoint).address.dropLast) ∘
        (fun candidate : input.LocalizedCIPOccurrenceFrame =>
          candidate.mapSpatialPoints mapPoint)) =
        (fun candidate : input.LocalizedCIPOccurrenceFrame =>
          candidate.root == frame.root &&
            candidate.address.length + 1 == frame.address.length &&
            candidate.address == frame.address.dropLast) := by
    funext candidate
    rfl
  rw [predicateEq]

@[simp] theorem localizedCarrierOutwardChildFrames_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    {fuel : Nat} (frame : input.LocalizedCIPOccurrenceFrame) :
    (input.mapSpatialPoints mapPoint).localizedCarrierOutwardChildFrames
        (fuel := fuel) (frame.mapSpatialPoints mapPoint) =
      (input.localizedCarrierOutwardChildFrames (fuel := fuel) frame).map
        (fun child => child.mapSpatialPoints mapPoint) := by
  unfold localizedCarrierOutwardChildFrames
  rw [localizedOccurrences_mapSpatialPoints, List.filter_map]
  have predicateEq :
      ((fun candidate : (input.mapSpatialPoints mapPoint).LocalizedCIPOccurrenceFrame =>
          candidate.root == (frame.mapSpatialPoints mapPoint).root &&
            candidate.address.length == (frame.mapSpatialPoints mapPoint).address.length + 1 &&
            candidate.address.dropLast == (frame.mapSpatialPoints mapPoint).address) ∘
        (fun candidate : input.LocalizedCIPOccurrenceFrame =>
          candidate.mapSpatialPoints mapPoint)) =
        (fun candidate : input.LocalizedCIPOccurrenceFrame =>
          candidate.root == frame.root &&
            candidate.address.length == frame.address.length + 1 &&
            candidate.address.dropLast == frame.address) := by
    funext candidate
    rfl
  rw [predicateEq]

@[simp] theorem localizedRerootNeighborFrames_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    {fuel : Nat} (frame : input.LocalizedCIPOccurrenceFrame) :
    (input.mapSpatialPoints mapPoint).localizedRerootNeighborFrames
        (fuel := fuel) (frame.mapSpatialPoints mapPoint) =
      (input.localizedRerootNeighborFrames (fuel := fuel) frame).map
        (fun neighbor => neighbor.mapSpatialPoints mapPoint) := by
  simp [localizedRerootNeighborFrames]

@[simp] theorem intendedLocalizedRerootChildFrames_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    {fuel : Nat} (cursor : input.LocalizedRerootCursor fuel) :
    (input.mapSpatialPoints mapPoint).intendedLocalizedRerootChildFrames
        (cursor.mapSpatialPoints mapPoint) =
      (input.intendedLocalizedRerootChildFrames cursor).map
        (fun child => child.mapSpatialPoints mapPoint) := by
  unfold intendedLocalizedRerootChildFrames
  simp only [LocalizedRerootCursor.mapSpatialPoints,
    LocalizedCIPOccurrence.mapSpatialPoints,
    LocalizedCIPOccurrenceFrame.mapSpatialPoints]
  by_cases duplicate : cursor.occurrence.1.node.isDuplicateLeaf
  · simp [duplicate]
  · simp only [if_neg duplicate]
    cases previousEq : cursor.previous? with
    | none =>
        change
          (input.mapSpatialPoints mapPoint).localizedRerootNeighborFrames
              (cursor.occurrence.1.mapSpatialPoints mapPoint) = _
        exact localizedRerootNeighborFrames_mapSpatialPoints input mapPoint _
    | some previous =>
        simp only [Option.map_some]
        change
          List.filter (fun frame => frame.address != previous.1.address)
              ((input.mapSpatialPoints mapPoint).localizedRerootNeighborFrames
                (cursor.occurrence.1.mapSpatialPoints mapPoint)) = _
        rw [localizedRerootNeighborFrames_mapSpatialPoints, List.filter_map]
        have predicateEq :
            ((fun frame : (input.mapSpatialPoints mapPoint).LocalizedCIPOccurrenceFrame =>
                frame.address != previous.1.address) ∘
              (fun frame : input.LocalizedCIPOccurrenceFrame =>
                frame.mapSpatialPoints mapPoint)) =
              (fun frame : input.LocalizedCIPOccurrenceFrame =>
                frame.address != previous.1.address) := by
          funext frame
          rfl
        rw [predicateEq]
        rfl

@[simp] theorem localizedRerootChildren?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    {fuel : Nat} (cursor : input.LocalizedRerootCursor fuel) :
    (input.mapSpatialPoints mapPoint).localizedRerootChildren?
        (cursor.mapSpatialPoints mapPoint) =
      (input.localizedRerootChildren? cursor).map
        (fun children => children.map
          (fun child => child.mapSpatialPoints mapPoint)) := by
  obtain ⟨children, childrenComputed⟩ := input.exists_localizedRerootChildren cursor
  rw [childrenComputed]
  simp only [Option.map_some]
  apply ((input.mapSpatialPoints mapPoint).localizedRerootChildren?_eq_some_iff
    (cursor.mapSpatialPoints mapPoint) _).2
  have derived := (input.localizedRerootChildren?_eq_some_iff cursor children).1
    childrenComputed
  constructor
  · calc
      (children.map (fun child => child.mapSpatialPoints mapPoint)).map
          (fun child => child.occurrence.1) =
        (children.map (fun child => child.occurrence.1)).map
          (fun frame => frame.mapSpatialPoints mapPoint) := by
            rw [List.map_map, List.map_map]
            apply List.map_congr_left
            intro child childPresent
            rfl
      _ = (input.intendedLocalizedRerootChildFrames cursor).map
          (fun frame => frame.mapSpatialPoints mapPoint) := by rw [derived.1]
      _ = (input.mapSpatialPoints mapPoint).intendedLocalizedRerootChildFrames
          (cursor.mapSpatialPoints mapPoint) :=
        (intendedLocalizedRerootChildFrames_mapSpatialPoints
          input mapPoint cursor).symm
  · intro child childPresent
    rw [List.mem_map] at childPresent
    rcases childPresent with ⟨original, originalPresent, rfl⟩
    simp only [LocalizedRerootCursor.mapSpatialPoints]
    rw [derived.2 original originalPresent]
    rfl

@[simp] theorem localizedRule3SpatialRootObservations_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (observation : Option input.LocalizedRule3SpatialNodeResult) :
    (input.mapSpatialPoints mapPoint).localizedRule3SpatialRootObservations
        (observation.map (fun result => result.mapSpatialPoints mapPoint)) =
      (input.localizedRule3SpatialRootObservations observation).map
        (fun layer => layer.map fun entry =>
          (entry.1, entry.2.mapSpatialPoints mapPoint)) := by
  cases observation <;> rfl

@[simp] theorem localizedRule3SpatialRootPriorities_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (observation : Option input.LocalizedRule3SpatialNodeResult) :
    (input.mapSpatialPoints mapPoint).localizedRule3SpatialRootPriorities
        (observation.map (fun result => result.mapSpatialPoints mapPoint)) =
      input.localizedRule3SpatialRootPriorities observation := by
  cases observation <;> rfl

@[simp] theorem insertLocalizedRerootRecursiveRule3SpatialKey_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey) :
    ∀ keys : List input.LocalizedRerootRecursiveRule3SpatialKey,
    (input.mapSpatialPoints mapPoint).insertLocalizedRerootRecursiveRule3SpatialKey
        (key.mapSpatialPoints mapPoint)
        (keys.map fun child => child.mapSpatialPoints mapPoint) =
      (input.insertLocalizedRerootRecursiveRule3SpatialKey key keys).map
        (fun child => child.mapSpatialPoints mapPoint)
  | [] => rfl
  | head :: tail => by
      simp only [List.map_cons]
      unfold insertLocalizedRerootRecursiveRule3SpatialKey
      rw [compareLocalizedRerootRecursiveRule3SpatialKeys_mapSpatialPoints]
      cases input.compareLocalizedRerootRecursiveRule3SpatialKeys key head <;>
        simp [insertLocalizedRerootRecursiveRule3SpatialKey_mapSpatialPoints]

@[simp] theorem sortLocalizedRerootRecursiveRule3SpatialKeys_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3) :
    ∀ keys : List input.LocalizedRerootRecursiveRule3SpatialKey,
    (input.mapSpatialPoints mapPoint).sortLocalizedRerootRecursiveRule3SpatialKeys
        (keys.map fun child => child.mapSpatialPoints mapPoint) =
      (input.sortLocalizedRerootRecursiveRule3SpatialKeys keys).map
        (fun child => child.mapSpatialPoints mapPoint)
  | [] => rfl
  | key :: keys => by
      simp only [List.map_cons]
      unfold sortLocalizedRerootRecursiveRule3SpatialKeys
      rw [sortLocalizedRerootRecursiveRule3SpatialKeys_mapSpatialPoints,
        insertLocalizedRerootRecursiveRule3SpatialKey_mapSpatialPoints]

@[simp] theorem localizedRerootRule3ObservationChildLayerCount_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3) :
    ∀ children : List input.LocalizedRerootRecursiveRule3SpatialKey,
    (input.mapSpatialPoints mapPoint).localizedRerootRule3ObservationChildLayerCount
        (children.map fun child => child.mapSpatialPoints mapPoint) =
      input.localizedRerootRule3ObservationChildLayerCount children
  | [] => rfl
  | child :: children => by
      unfold localizedRerootRule3ObservationChildLayerCount
      simp only [List.map_cons, List.foldl_cons,
        LocalizedRerootRecursiveRule3SpatialKey.mapSpatialPoints, List.length_map]
      generalize initial : child.observations.length = accumulator
      clear initial
      induction children generalizing accumulator with
      | nil => rfl
      | cons next tail ih =>
          simp only [List.map_cons, List.foldl_cons,
            List.length_map]
          exact ih _

@[simp] theorem localizedRerootRule3PriorityChildLayerCount_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3) :
    ∀ children : List input.LocalizedRerootRecursiveRule3SpatialKey,
    (input.mapSpatialPoints mapPoint).localizedRerootRule3PriorityChildLayerCount
        (children.map fun child => child.mapSpatialPoints mapPoint) =
      input.localizedRerootRule3PriorityChildLayerCount children
  | [] => rfl
  | child :: children => by
      unfold localizedRerootRule3PriorityChildLayerCount
      simp only [List.map_cons, List.foldl_cons,
        LocalizedRerootRecursiveRule3SpatialKey.mapSpatialPoints]
      generalize initial : child.rule3.length = accumulator
      clear initial
      induction children generalizing accumulator with
      | nil => rfl
      | cons next tail ih =>
          simp only [List.map_cons, List.foldl_cons]
          exact ih _

@[simp] theorem mergeLocalizedRerootRule3PriorityChildren_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (children : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    (input.mapSpatialPoints mapPoint).mergeLocalizedRerootRule3PriorityChildren
        (children.map fun child => child.mapSpatialPoints mapPoint) =
      input.mergeLocalizedRerootRule3PriorityChildren children := by
  unfold mergeLocalizedRerootRule3PriorityChildren
  rw [localizedRerootRule3PriorityChildLayerCount_mapSpatialPoints]
  apply List.map_congr_left
  intro depth depthPresent
  rw [List.zipIdx_map, List.flatMap_map]
  apply List.flatMap_congr
  intro child childPresent
  cases child
  rfl

@[simp] theorem mergeLocalizedRerootRule3ObservationChildren_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (children : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    (input.mapSpatialPoints mapPoint).mergeLocalizedRerootRule3ObservationChildren
        (children.map fun child => child.mapSpatialPoints mapPoint) =
      (input.mergeLocalizedRerootRule3ObservationChildren children).map
        (fun layer => layer.map fun entry =>
          (entry.1, entry.2.mapSpatialPoints mapPoint)) := by
  unfold mergeLocalizedRerootRule3ObservationChildren
  rw [localizedRerootRule3ObservationChildLayerCount_mapSpatialPoints]
  rw [List.map_map]
  apply List.map_congr_left
  intro depth depthPresent
  simp only [Function.comp_apply]
  rw [List.zipIdx_map, List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro child childPresent
  cases child with
  | mk child slot =>
      change
        OfficialRuleMajorKey.prefixLayer slot
            ((child.observations.map fun layer => layer.map fun entry =>
              (entry.1, entry.2.mapSpatialPoints mapPoint)).getD depth []) =
          (OfficialRuleMajorKey.prefixLayer slot
            (child.observations.getD depth [])).map
              (fun entry => (entry.1, entry.2.mapSpatialPoints mapPoint))
      unfold List.getD
      rw [List.getElem?_map]
      cases layerEq : child.observations[depth]? with
      | none => rfl
      | some layer =>
          change
            OfficialRuleMajorKey.prefixLayer slot
                (layer.map (OfficialRuleMajorKey.mapObservation
                  (fun result : input.LocalizedRule3SpatialNodeResult =>
                    result.mapSpatialPoints mapPoint))) =
              (OfficialRuleMajorKey.prefixLayer slot layer).map
                (OfficialRuleMajorKey.mapObservation
                  (fun result : input.LocalizedRule3SpatialNodeResult =>
                    result.mapSpatialPoints mapPoint))
          exact OfficialRuleMajorKey.prefixLayer_mapObservation
            (fun result : input.LocalizedRule3SpatialNodeResult =>
              result.mapSpatialPoints mapPoint) slot layer

theorem listMapM_map_of_natural {α β γ δ : Type*}
    (mapInput : α → β) (mapOutput : γ → δ)
    (source : α → Option γ) (target : β → Option δ)
    (natural : ∀ value, target (mapInput value) = (source value).map mapOutput) :
    ∀ values : List α,
      values.mapM (target ∘ mapInput) =
        (values.mapM source).map (List.map mapOutput)
  | [] => rfl
  | value :: values => by
      simp only [List.mapM_cons, Function.comp_apply]
      rw [natural value, listMapM_map_of_natural _ _ _ _ natural values]
      cases source value <;> cases values.mapM source <;> rfl

/-- The complete recursive Rules-1a--3 key compiler commutes with every invertible affine
coordinate change. -/
theorem buildLocalizedRerootRecursiveRule3SpatialKey?_affine
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (transform : RationalAffineFrameTransform)
    (determinantNonzero : transform.determinant ≠ 0) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
    (input.mapSpatialPoints transform.applyPoint).buildLocalizedRerootRecursiveRule3SpatialKey?
        fuel
          (cursor.mapSpatialPoints transform.applyPoint) =
      (input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel cursor).map
        (fun key => key.mapSpatialPoints transform.applyPoint)
  | 0, cursor => by
      unfold buildLocalizedRerootRecursiveRule3SpatialKey?
      rw [localizedRerootChildren?_mapSpatialPoints]
      have nodeEq :
          (cursor.mapSpatialPoints transform.applyPoint).occurrence.1.node =
            cursor.occurrence.1.node := rfl
      rw [nodeEq,
        localizedRule3SpatialNode?_affine input cursor.occurrence.1.node
          transform determinantNonzero]
      cases childrenEq : input.localizedRerootChildren? cursor with
      | none => rfl
      | some children =>
          cases observationEq : input.localizedRule3SpatialNode?
              cursor.occurrence.1.node with
          | none => rfl
          | some observation =>
              by_cases terminal : children = []
              · simp [terminal, moleculeGraph_mapSpatialPoints,
                  localizedRule3SpatialRootObservations_mapSpatialPoints,
                  localizedRule3SpatialRootPriorities_mapSpatialPoints,
                  LocalizedRerootRecursiveRule3SpatialKey.mapSpatialPoints]
              · simp [terminal]
  | fuel + 1, cursor => by
      unfold buildLocalizedRerootRecursiveRule3SpatialKey?
      rw [localizedRerootChildren?_mapSpatialPoints]
      have nodeEq :
          (cursor.mapSpatialPoints transform.applyPoint).occurrence.1.node =
            cursor.occurrence.1.node := rfl
      rw [nodeEq,
        localizedRule3SpatialNode?_affine input cursor.occurrence.1.node
          transform determinantNonzero]
      cases childrenEq : input.localizedRerootChildren? cursor with
      | none => rfl
      | some children =>
          cases observationEq : input.localizedRule3SpatialNode?
              cursor.occurrence.1.node with
          | none => rfl
          | some observation =>
              by_cases terminal : children = []
              · simp [terminal, moleculeGraph_mapSpatialPoints,
                  localizedRule3SpatialRootObservations_mapSpatialPoints,
                  localizedRule3SpatialRootPriorities_mapSpatialPoints,
                  LocalizedRerootRecursiveRule3SpatialKey.mapSpatialPoints]
              · simp [terminal]
                have mapMNatural :
                    children.mapM
                        (buildLocalizedRerootRecursiveRule3SpatialKey?
                          (input.mapSpatialPoints transform.applyPoint) fuel ∘
                            fun child =>
                              child.mapSpatialPoints transform.applyPoint) =
                      (children.mapM
                        (input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel)).map
                        (fun keys => keys.map fun key =>
                          key.mapSpatialPoints transform.applyPoint) :=
                  listMapM_map_of_natural
                    (fun child => child.mapSpatialPoints transform.applyPoint)
                    (fun key => key.mapSpatialPoints transform.applyPoint)
                    (input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel)
                    (buildLocalizedRerootRecursiveRule3SpatialKey?
                      (input.mapSpatialPoints transform.applyPoint) fuel)
                    (fun child =>
                      buildLocalizedRerootRecursiveRule3SpatialKey?_affine
                        input transform determinantNonzero fuel child)
                    children
                rw [mapMNatural]
                cases childKeysEq : children.mapM
                    (input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel) with
                | none => rfl
                | some childKeys =>
                    simp only [Option.map_some, Option.bind_some]
                    rw [sortLocalizedRerootRecursiveRule3SpatialKeys_mapSpatialPoints]
                    rw [
                      mergeLocalizedRerootRule3ObservationChildren_mapSpatialPoints,
                      mergeLocalizedRerootRule3PriorityChildren_mapSpatialPoints]
                    simp only [LocalizedRerootRecursiveRule3SpatialKey.mapSpatialPoints,
                      List.map_append, List.map_map]
                    rfl

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
