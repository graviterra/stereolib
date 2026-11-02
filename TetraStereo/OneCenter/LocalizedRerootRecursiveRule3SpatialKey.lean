import TetraStereo.OneCenter.LocalizedRerootRule3SpatialKey

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Recursively ranked localized Rule-3 spatial keys

The earlier `LocalizedRerootUncancelledRule3SpatialKey` deliberately exposed a boundary: it
scanned a tree whose siblings had already been sorted by Rules 1a--2 alone.  If two siblings were
constitutionally equivalent but carried different Rule-3 observations, their source enumeration
could therefore leak into the flattened Rule-3 signature.

This module closes that ordering gap bottom-up.  Every child is first compiled through Rules
1a--3, siblings are sorted by that complete cumulative key, and only then are sibling-slot
addresses assigned at the parent.  A genuine order-two occurrence whose spatial reading is
unresolved still refuses the entire key.  The result remains `Uncancelled`: identity-aware
cancellation of shared/cyclic physical geometrical units is a separate, subsequent layer.
-/

namespace CertifiedLocalizedCIPInput

/-- Independent meaning of one successfully resolved node observation. -/
inductive DeclarativeLocalizedRule3SpatialNodeOutcome
    (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) :
    Option input.LocalizedRule3SpatialNodeResult → Prop
  | structuralNonunit
      (notUnit : ¬ input.LocalizedRule3NodeHasDoubleBondEdge node) :
      input.DeclarativeLocalizedRule3SpatialNodeOutcome node none
  | geometry {result : input.LocalizedRule3SpatialNodeResult}
      (observed : input.DeclarativeLocalizedRule3SpatialNode node result) :
      input.DeclarativeLocalizedRule3SpatialNodeOutcome node (some result)

/-- Every successful executable node reading has its independent structural meaning. -/
theorem localizedRule3SpatialNode?_outcome_sound
    (input : CertifiedLocalizedCIPInput) (node : OfficialCIPNode input.Atom)
    (outcome : Option input.LocalizedRule3SpatialNodeResult)
    (computed : input.localizedRule3SpatialNode? node = some outcome) :
    input.DeclarativeLocalizedRule3SpatialNodeOutcome node outcome := by
  cases outcome with
  | none =>
      exact DeclarativeLocalizedRule3SpatialNodeOutcome.structuralNonunit
        (input.localizedRule3SpatialNode?_eq_some_none_implies_not_edge node computed)
  | some result =>
      exact DeclarativeLocalizedRule3SpatialNodeOutcome.geometry
        (input.localizedRule3SpatialNode?_sound node result computed)

/-- Exact Rule-3 observation at a root.  Structural nonunits contribute no geometrical unit. -/
def localizedRule3SpatialRootObservations
    (input : CertifiedLocalizedCIPInput) :
    Option input.LocalizedRule3SpatialNodeResult →
      List (List (OfficialSparseEntry input.LocalizedRule3SpatialNodeResult))
  | none => []
  | some result => [[([], result)]]

/-- Priority projection of the same optional root observation. -/
def localizedRule3SpatialRootPriorities
    (input : CertifiedLocalizedCIPInput) :
    Option input.LocalizedRule3SpatialNodeResult →
      List (List (OfficialSparseEntry Nat))
  | none => []
  | some result => [[([], result.unit.geometry.priority)]]

/-- A bottom-up Rules-1a--3 key before shared/cyclic physical-unit cancellation. -/
structure LocalizedRerootRecursiveRule3SpatialKey
    (input : CertifiedLocalizedCIPInput) where
  constitutional : OfficialRuleMajorKey input.Atom
  observations : List (List
    (OfficialSparseEntry input.LocalizedRule3SpatialNodeResult))
  rule3 : List (List (OfficialSparseEntry Nat))

/-- Rules 1a--2 decide first; only an exhaustive constitutional tie exposes Rule 3. -/
def compareLocalizedRerootRecursiveRule3SpatialKeys
    (input : CertifiedLocalizedCIPInput) :
    input.LocalizedRerootRecursiveRule3SpatialKey →
      input.LocalizedRerootRecursiveRule3SpatialKey → Ordering :=
  compareLex
    (Ordering.byKey (fun key => key.constitutional) OfficialRuleMajorKey.compare)
    (Ordering.byKey (fun key => key.rule3)
      (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat))

/-- The cumulative Rules-1a--3 comparator is oriented and transitive. -/
theorem compareLocalizedRerootRecursiveRule3SpatialKeys_transCmp
    (input : CertifiedLocalizedCIPInput) :
    Std.TransCmp input.compareLocalizedRerootRecursiveRule3SpatialKeys := by
  letI : Std.TransCmp (@OfficialRuleMajorKey.compare input.Atom) :=
    OfficialRuleMajorKey.compare_transCmp
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  unfold compareLocalizedRerootRecursiveRule3SpatialKeys
    OfficialRuleMajorKey.compareSparseLayers
    OfficialRuleMajorKey.compareSparseLayer
    OfficialRuleMajorKey.compareSparseEntry
  infer_instance

@[simp] theorem compareLocalizedRerootRecursiveRule3SpatialKeys_of_constitutional_gt
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootRecursiveRule3SpatialKey)
    (strict : OfficialRuleMajorKey.compare left.constitutional right.constitutional =
      Ordering.gt) :
    input.compareLocalizedRerootRecursiveRule3SpatialKeys left right = Ordering.gt := by
  simp [compareLocalizedRerootRecursiveRule3SpatialKeys, compareLex, strict,
    Ordering.byKey]

@[simp] theorem compareLocalizedRerootRecursiveRule3SpatialKeys_of_constitutional_eq
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootRecursiveRule3SpatialKey)
    (tied : OfficialRuleMajorKey.compare left.constitutional right.constitutional =
      Ordering.eq) :
    input.compareLocalizedRerootRecursiveRule3SpatialKeys left right =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        left.rule3 right.rule3 := by
  simp [compareLocalizedRerootRecursiveRule3SpatialKeys, compareLex, tied,
    Ordering.byKey]

/-- Structural descending insertion by the complete cumulative Rules-1a--3 comparator. -/
def insertLocalizedRerootRecursiveRule3SpatialKey
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey) :
    List input.LocalizedRerootRecursiveRule3SpatialKey →
      List input.LocalizedRerootRecursiveRule3SpatialKey
  | [] => [key]
  | head :: tail =>
      match input.compareLocalizedRerootRecursiveRule3SpatialKeys key head with
      | .lt => head :: input.insertLocalizedRerootRecursiveRule3SpatialKey key tail
      | .eq | .gt => key :: head :: tail

/-- Structural descending sort used before a parent assigns sibling addresses. -/
def sortLocalizedRerootRecursiveRule3SpatialKeys
    (input : CertifiedLocalizedCIPInput) :
    List input.LocalizedRerootRecursiveRule3SpatialKey →
      List input.LocalizedRerootRecursiveRule3SpatialKey
  | [] => []
  | key :: keys =>
      input.insertLocalizedRerootRecursiveRule3SpatialKey key
        (input.sortLocalizedRerootRecursiveRule3SpatialKeys keys)

theorem insertLocalizedRerootRecursiveRule3SpatialKey_perm
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey) :
    ∀ keys,
      (input.insertLocalizedRerootRecursiveRule3SpatialKey key keys).Perm (key :: keys)
  | [] => List.Perm.refl _
  | head :: tail => by
      unfold insertLocalizedRerootRecursiveRule3SpatialKey
      cases comparison : input.compareLocalizedRerootRecursiveRule3SpatialKeys key head with
      | eq => exact List.Perm.refl _
      | gt => exact List.Perm.refl _
      | lt =>
          exact (List.Perm.cons head
            (input.insertLocalizedRerootRecursiveRule3SpatialKey_perm key tail)).trans
              (List.Perm.swap key head tail)

theorem sortLocalizedRerootRecursiveRule3SpatialKeys_perm
    (input : CertifiedLocalizedCIPInput) :
    ∀ keys,
      (input.sortLocalizedRerootRecursiveRule3SpatialKeys keys).Perm keys
  | [] => List.Perm.refl []
  | key :: keys =>
      (input.insertLocalizedRerootRecursiveRule3SpatialKey_perm key
        (input.sortLocalizedRerootRecursiveRule3SpatialKeys keys)).trans
          (List.Perm.cons key
            (input.sortLocalizedRerootRecursiveRule3SpatialKeys_perm keys))

/-- Every earlier sibling has priority at least as high as every later sibling. -/
def LocalizedRerootRecursiveRule3SpatialKeysDescending
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) : Prop :=
  keys.Pairwise fun left right =>
    input.compareLocalizedRerootRecursiveRule3SpatialKeys left right ≠ Ordering.lt

theorem insertLocalizedRerootRecursiveRule3SpatialKey_descending
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey) :
    ∀ keys,
      input.LocalizedRerootRecursiveRule3SpatialKeysDescending keys →
      input.LocalizedRerootRecursiveRule3SpatialKeysDescending
        (input.insertLocalizedRerootRecursiveRule3SpatialKey key keys)
  | [], _ => by
      simp [insertLocalizedRerootRecursiveRule3SpatialKey,
        LocalizedRerootRecursiveRule3SpatialKeysDescending]
  | head :: tail, sorted => by
      letI : Std.TransCmp input.compareLocalizedRerootRecursiveRule3SpatialKeys :=
        input.compareLocalizedRerootRecursiveRule3SpatialKeys_transCmp
      have headOverTail : ∀ observed ∈ tail,
          input.compareLocalizedRerootRecursiveRule3SpatialKeys head observed ≠ Ordering.lt :=
        (List.pairwise_cons.mp sorted).1
      have tailSorted : input.LocalizedRerootRecursiveRule3SpatialKeysDescending tail :=
        (List.pairwise_cons.mp sorted).2
      unfold insertLocalizedRerootRecursiveRule3SpatialKey
      cases comparison : input.compareLocalizedRerootRecursiveRule3SpatialKeys key head with
      | gt =>
          rw [LocalizedRerootRecursiveRule3SpatialKeysDescending, List.pairwise_cons]
          constructor
          · intro observed present
            rcases List.mem_cons.mp present with rfl | tailPresent
            · simp [comparison]
            · exact Std.TransCmp.ge_trans (by simp [comparison])
                (headOverTail observed tailPresent)
          · exact sorted
      | eq =>
          rw [LocalizedRerootRecursiveRule3SpatialKeysDescending, List.pairwise_cons]
          constructor
          · intro observed present
            rcases List.mem_cons.mp present with rfl | tailPresent
            · simp [comparison]
            · exact Std.TransCmp.ge_trans (by simp [comparison])
                (headOverTail observed tailPresent)
          · exact sorted
      | lt =>
          have insertedSorted :=
            input.insertLocalizedRerootRecursiveRule3SpatialKey_descending
              key tail tailSorted
          rw [LocalizedRerootRecursiveRule3SpatialKeysDescending, List.pairwise_cons]
          constructor
          · intro observed present
            have permutation :=
              input.insertLocalizedRerootRecursiveRule3SpatialKey_perm key tail
            have sourcePresent : observed ∈ key :: tail :=
              (permutation.mem_iff).mp present
            rcases List.mem_cons.mp sourcePresent with same | tailPresent
            · subst observed
              have reverse :
                  input.compareLocalizedRerootRecursiveRule3SpatialKeys head key =
                    Ordering.gt := by
                rw [Std.OrientedCmp.gt_iff_lt]
                exact comparison
              exact by simp [reverse]
            · exact headOverTail observed tailPresent
          · exact insertedSorted

theorem sortLocalizedRerootRecursiveRule3SpatialKeys_descending
    (input : CertifiedLocalizedCIPInput) :
    ∀ keys,
      input.LocalizedRerootRecursiveRule3SpatialKeysDescending
        (input.sortLocalizedRerootRecursiveRule3SpatialKeys keys)
  | [] => by
      simp [sortLocalizedRerootRecursiveRule3SpatialKeys,
        LocalizedRerootRecursiveRule3SpatialKeysDescending]
  | key :: keys =>
      input.insertLocalizedRerootRecursiveRule3SpatialKey_descending key
        (input.sortLocalizedRerootRecursiveRule3SpatialKeys keys)
        (input.sortLocalizedRerootRecursiveRule3SpatialKeys_descending keys)

/-- Maximum observation-sequence depth among recursively ranked children. -/
def localizedRerootRule3ObservationChildLayerCount
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootRecursiveRule3SpatialKey) : Nat :=
  children.foldl (fun longest child => max longest child.observations.length) 0

/-- Merge physical-unit observations beneath their final cumulative sibling slots. -/
def mergeLocalizedRerootRule3ObservationChildren
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    List (List (OfficialSparseEntry input.LocalizedRule3SpatialNodeResult)) :=
  let count := input.localizedRerootRule3ObservationChildLayerCount children
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      OfficialRuleMajorKey.prefixLayer child.2
        (child.1.observations.getD depth [])

/-- Maximum Rule-3 priority-sequence depth among recursively ranked children. -/
def localizedRerootRule3PriorityChildLayerCount
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootRecursiveRule3SpatialKey) : Nat :=
  children.foldl (fun longest child => max longest child.rule3.length) 0

/-- Merge Rule-3 priorities beneath the same final cumulative sibling slots. -/
def mergeLocalizedRerootRule3PriorityChildren
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    List (List (OfficialSparseEntry Nat)) :=
  let count := input.localizedRerootRule3PriorityChildLayerCount children
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      OfficialRuleMajorKey.prefixLayer child.2 (child.1.rule3.getD depth [])

/-- Compile the reroot tree bottom-up, refusing unresolved genuine geometrical units. -/
noncomputable def buildLocalizedRerootRecursiveRule3SpatialKey?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    Nat → input.LocalizedRerootCursor carrierFuel →
      Option input.LocalizedRerootRecursiveRule3SpatialKey
  | 0, cursor => do
      let children ← input.localizedRerootChildren? cursor
      let observation ← input.localizedRule3SpatialNode? cursor.occurrence.1.node
      if children = [] then
        some
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := input.localizedRule3SpatialRootObservations observation
            rule3 := input.localizedRule3SpatialRootPriorities observation }
      else none
  | fuel + 1, cursor => do
      let children ← input.localizedRerootChildren? cursor
      let observation ← input.localizedRule3SpatialNode? cursor.occurrence.1.node
      if children = [] then
        some
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := input.localizedRule3SpatialRootObservations observation
            rule3 := input.localizedRule3SpatialRootPriorities observation }
      else
        let childKeys ← children.mapM
          (input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel)
        let sorted := input.sortLocalizedRerootRecursiveRule3SpatialKeys childKeys
        some
          { constitutional := OfficialRuleMajorKey.assemble
              (input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            observations := input.localizedRule3SpatialRootObservations observation ++
              input.mergeLocalizedRerootRule3ObservationChildren sorted
            rule3 := input.localizedRule3SpatialRootPriorities observation ++
              input.mergeLocalizedRerootRule3PriorityChildren sorted }

/-- Numeric Rule-3 observations are an exact projection of retained physical-unit evidence. -/
def LocalizedRerootRecursiveRule3SpatialKey.Rule3Aligned
    {input : CertifiedLocalizedCIPInput}
    (key : input.LocalizedRerootRecursiveRule3SpatialKey) : Prop :=
  key.rule3 = OfficialRuleMajorKey.mapSourceLayers
    (fun result => result.unit.geometry.priority) key.observations

theorem localizedRule3SpatialRootPriorities_eq_map_observations
    (input : CertifiedLocalizedCIPInput)
    (observation : Option input.LocalizedRule3SpatialNodeResult) :
    input.localizedRule3SpatialRootPriorities observation =
      OfficialRuleMajorKey.mapSourceLayers
        (fun result => result.unit.geometry.priority)
        (input.localizedRule3SpatialRootObservations observation) := by
  cases observation <;> rfl

theorem localizedRerootRule3PriorityChildLayerCount_eq_observation
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (aligned : ∀ child, child ∈ children → child.Rule3Aligned) :
    input.localizedRerootRule3PriorityChildLayerCount children =
      input.localizedRerootRule3ObservationChildLayerCount children := by
  unfold localizedRerootRule3PriorityChildLayerCount
    localizedRerootRule3ObservationChildLayerCount
  have generalized : ∀ initial,
      List.foldl (fun longest child => max longest child.rule3.length)
          initial children =
        List.foldl (fun longest child => max longest child.observations.length)
          initial children := by
    induction children with
    | nil => intro initial; rfl
    | cons child children ih =>
        intro initial
        simp only [List.foldl_cons]
        have childAligned := aligned child (by simp)
        have tailAligned : ∀ tail, tail ∈ children → tail.Rule3Aligned := by
          intro tail present
          exact aligned tail (by simp [present])
        rw [childAligned]
        simp only [OfficialRuleMajorKey.mapSourceLayers, List.length_map]
        exact ih tailAligned _
  exact generalized 0

/-- Child merging commutes with the evidence-to-priority projection, including empty padding. -/
theorem mergeLocalizedRerootRule3PriorityChildren_eq_map_observations
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (aligned : ∀ child, child ∈ children → child.Rule3Aligned) :
    input.mergeLocalizedRerootRule3PriorityChildren children =
      OfficialRuleMajorKey.mapSourceLayers
        (fun result => result.unit.geometry.priority)
        (input.mergeLocalizedRerootRule3ObservationChildren children) := by
  unfold mergeLocalizedRerootRule3PriorityChildren
    mergeLocalizedRerootRule3ObservationChildren
    OfficialRuleMajorKey.mapSourceLayers
  rw [input.localizedRerootRule3PriorityChildLayerCount_eq_observation
    children aligned]
  rw [List.map_map]
  apply List.map_congr_left
  intro depth present
  simp only [Function.comp_apply]
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro child childPresent
  have keyPresent : child.1 ∈ children := List.fst_mem_of_mem_zipIdx childPresent
  rw [aligned child.1 keyPresent]
  rw [OfficialRuleMajorKey.mapSourceLayers_getD]
  rw [OfficialRuleMajorKey.prefixLayer_mapObservation]

private theorem mapM_buildLocalizedRerootRecursiveRule3SpatialKey?_member
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat} :
    ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel))
      (keys : List input.LocalizedRerootRecursiveRule3SpatialKey),
      cursors.mapM (input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel) = some keys →
      ∀ key, key ∈ keys →
        ∃ cursor, cursor ∈ cursors ∧
          input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel cursor = some key
  | [], keys, computed, key, present => by
      simp at computed
      subst keys
      simp at present
  | cursor :: cursors, keys, computed, key, present => by
      rw [List.mapM_cons] at computed
      cases headComputed : input.buildLocalizedRerootRecursiveRule3SpatialKey?
          fuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              rcases List.mem_cons.mp present with rfl | tailPresent
              · exact ⟨cursor, by simp, headComputed⟩
              · rcases input.mapM_buildLocalizedRerootRecursiveRule3SpatialKey?_member
                    cursors tail tailComputed key tailPresent with
                  ⟨source, sourcePresent, sourceComputed⟩
                exact ⟨source, List.mem_cons_of_mem cursor sourcePresent, sourceComputed⟩

/-- Every successful recursive Rule-3 key has a complete constitutional component. -/
theorem buildLocalizedRerootRecursiveRule3SpatialKey?_constitutional_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootRecursiveRule3SpatialKey),
      input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel cursor = some key →
      key.constitutional.complete = true
  | 0, cursor, key, computed => by
      unfold buildLocalizedRerootRecursiveRule3SpatialKey? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          cases observationComputed :
              input.localizedRule3SpatialNode? cursor.occurrence.1.node with
          | none => simp [childrenComputed, observationComputed] at computed
          | some observation =>
              by_cases terminal : children = []
              · simp [childrenComputed, observationComputed, terminal] at computed
                subst key
                rfl
              · simp [childrenComputed, observationComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildLocalizedRerootRecursiveRule3SpatialKey? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          cases observationComputed :
              input.localizedRule3SpatialNode? cursor.occurrence.1.node with
          | none => simp [childrenComputed, observationComputed] at computed
          | some observation =>
              by_cases terminal : children = []
              · simp [childrenComputed, observationComputed, terminal] at computed
                subst key
                rfl
              · cases childKeysComputed : children.mapM
                    (input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel) with
                | none =>
                    simp [childrenComputed, observationComputed, terminal,
                      childKeysComputed] at computed
                | some childKeys =>
                    simp [childrenComputed, observationComputed, terminal,
                      childKeysComputed] at computed
                    subst key
                    unfold OfficialRuleMajorKey.assemble
                    rw [List.all_eq_true]
                    intro childConstitutional childPresent
                    rw [List.mem_map] at childPresent
                    rcases childPresent with ⟨child, childSortedPresent, rfl⟩
                    have childSourcePresent : child ∈ childKeys :=
                      (input.sortLocalizedRerootRecursiveRule3SpatialKeys_perm
                        childKeys).mem_iff.mp childSortedPresent
                    rcases input.mapM_buildLocalizedRerootRecursiveRule3SpatialKey?_member
                        children childKeys childKeysComputed child childSourcePresent with
                      ⟨childCursor, _cursorPresent, childComputed⟩
                    exact input.buildLocalizedRerootRecursiveRule3SpatialKey?_constitutional_complete
                      fuel childCursor child childComputed

/-- Every successful constitutional cache is a fresh exact projection of its source nodes. -/
theorem buildLocalizedRerootRecursiveRule3SpatialKey?_constitutional_sourceAligned
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootRecursiveRule3SpatialKey),
      input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel cursor = some key →
      OfficialRuleMajorKey.SourceAligned input.moleculeGraph key.constitutional
  | 0, cursor, key, computed => by
      unfold buildLocalizedRerootRecursiveRule3SpatialKey? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          cases observationComputed :
              input.localizedRule3SpatialNode? cursor.occurrence.1.node with
          | none => simp [childrenComputed, observationComputed] at computed
          | some observation =>
              by_cases terminal : children = []
              · simp [childrenComputed, observationComputed, terminal] at computed
                subst key
                exact input.moleculeGraph.officialRuleMajorRootKey_sourceAligned
                  cursor.occurrence.1.node true
              · simp [childrenComputed, observationComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildLocalizedRerootRecursiveRule3SpatialKey? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          cases observationComputed :
              input.localizedRule3SpatialNode? cursor.occurrence.1.node with
          | none => simp [childrenComputed, observationComputed] at computed
          | some observation =>
              by_cases terminal : children = []
              · simp [childrenComputed, observationComputed, terminal] at computed
                subst key
                exact input.moleculeGraph.officialRuleMajorRootKey_sourceAligned
                  cursor.occurrence.1.node true
              · cases childKeysComputed : children.mapM
                    (input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel) with
                | none =>
                    simp [childrenComputed, observationComputed, terminal,
                      childKeysComputed] at computed
                | some childKeys =>
                    simp [childrenComputed, observationComputed, terminal,
                      childKeysComputed] at computed
                    subst key
                    apply OfficialRuleMajorKey.SourceAligned.assemble
                    · exact input.moleculeGraph.officialRuleMajorRootKey_sourceAligned
                        cursor.occurrence.1.node false
                    · intro childConstitutional childPresent
                      rw [List.mem_map] at childPresent
                      rcases childPresent with ⟨child, childSortedPresent, rfl⟩
                      have childSourcePresent : child ∈ childKeys :=
                        (input.sortLocalizedRerootRecursiveRule3SpatialKeys_perm
                          childKeys).mem_iff.mp childSortedPresent
                      rcases input.mapM_buildLocalizedRerootRecursiveRule3SpatialKey?_member
                          children childKeys childKeysComputed child childSourcePresent with
                        ⟨childCursor, _cursorPresent, childComputed⟩
                      exact input.buildLocalizedRerootRecursiveRule3SpatialKey?_constitutional_sourceAligned
                        fuel childCursor child childComputed

/-- Every successful numeric Rule-3 cache is exactly aligned with retained unit identities. -/
theorem buildLocalizedRerootRecursiveRule3SpatialKey?_rule3Aligned
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootRecursiveRule3SpatialKey),
      input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel cursor = some key →
      key.Rule3Aligned
  | 0, cursor, key, computed => by
      unfold buildLocalizedRerootRecursiveRule3SpatialKey? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          cases observationComputed :
              input.localizedRule3SpatialNode? cursor.occurrence.1.node with
          | none => simp [childrenComputed, observationComputed] at computed
          | some observation =>
              by_cases terminal : children = []
              · simp [childrenComputed, observationComputed, terminal] at computed
                subst key
                change input.localizedRule3SpatialRootPriorities observation =
                  OfficialRuleMajorKey.mapSourceLayers
                    (fun result => result.unit.geometry.priority)
                    (input.localizedRule3SpatialRootObservations observation)
                exact input.localizedRule3SpatialRootPriorities_eq_map_observations
                  observation
              · simp [childrenComputed, observationComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildLocalizedRerootRecursiveRule3SpatialKey? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          cases observationComputed :
              input.localizedRule3SpatialNode? cursor.occurrence.1.node with
          | none => simp [childrenComputed, observationComputed] at computed
          | some observation =>
              by_cases terminal : children = []
              · simp [childrenComputed, observationComputed, terminal] at computed
                subst key
                change input.localizedRule3SpatialRootPriorities observation =
                  OfficialRuleMajorKey.mapSourceLayers
                    (fun result => result.unit.geometry.priority)
                    (input.localizedRule3SpatialRootObservations observation)
                exact input.localizedRule3SpatialRootPriorities_eq_map_observations
                  observation
              · cases childKeysComputed : children.mapM
                    (input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel) with
                | none =>
                    simp [childrenComputed, observationComputed, terminal,
                      childKeysComputed] at computed
                | some childKeys =>
                    simp [childrenComputed, observationComputed, terminal,
                      childKeysComputed] at computed
                    subst key
                    change input.localizedRule3SpatialRootPriorities observation ++
                        input.mergeLocalizedRerootRule3PriorityChildren
                          (input.sortLocalizedRerootRecursiveRule3SpatialKeys childKeys) =
                      OfficialRuleMajorKey.mapSourceLayers
                        (fun result => result.unit.geometry.priority)
                        (input.localizedRule3SpatialRootObservations observation ++
                          input.mergeLocalizedRerootRule3ObservationChildren
                            (input.sortLocalizedRerootRecursiveRule3SpatialKeys childKeys))
                    rw [OfficialRuleMajorKey.mapSourceLayers_append]
                    rw [input.localizedRule3SpatialRootPriorities_eq_map_observations]
                    congr 1
                    apply input.mergeLocalizedRerootRule3PriorityChildren_eq_map_observations
                    intro child childSortedPresent
                    have childSourcePresent : child ∈ childKeys :=
                      (input.sortLocalizedRerootRecursiveRule3SpatialKeys_perm
                        childKeys).mem_iff.mp childSortedPresent
                    rcases input.mapM_buildLocalizedRerootRecursiveRule3SpatialKey?_member
                        children childKeys childKeysComputed child childSourcePresent with
                      ⟨childCursor, _cursorPresent, childComputed⟩
                    exact input.buildLocalizedRerootRecursiveRule3SpatialKey?_rule3Aligned
                      fuel childCursor child childComputed

mutual
  /-- Independent bottom-up derivation of a successful cumulative Rules-1a--3 key. -/
  inductive DeclarativeLocalizedRerootRecursiveRule3SpatialKey
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
      Nat → input.LocalizedRerootCursor carrierFuel →
        input.LocalizedRerootRecursiveRule3SpatialKey → Prop
    | terminal {fuel cursor children observation}
        (frame : input.DeclarativeLocalizedRerootChildren cursor children)
        (empty : children = [])
        (observed : input.DeclarativeLocalizedRule3SpatialNodeOutcome
          cursor.occurrence.1.node observation) :
        input.DeclarativeLocalizedRerootRecursiveRule3SpatialKey fuel cursor
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := input.localizedRule3SpatialRootObservations observation
            rule3 := input.localizedRule3SpatialRootPriorities observation }
    | branch {fuel cursor children observation childKeys sorted}
        (frame : input.DeclarativeLocalizedRerootChildren cursor children)
        (nonempty : children ≠ [])
        (observed : input.DeclarativeLocalizedRule3SpatialNodeOutcome
          cursor.occurrence.1.node observation)
        (childDerivations : input.DeclarativeLocalizedRerootRecursiveRule3SpatialKeyList
          fuel children childKeys)
        (ranking : sorted.Perm childKeys)
        (descending : input.LocalizedRerootRecursiveRule3SpatialKeysDescending sorted) :
        input.DeclarativeLocalizedRerootRecursiveRule3SpatialKey (fuel + 1) cursor
          { constitutional := OfficialRuleMajorKey.assemble
              (input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            observations := input.localizedRule3SpatialRootObservations observation ++
              input.mergeLocalizedRerootRule3ObservationChildren sorted
            rule3 := input.localizedRule3SpatialRootPriorities observation ++
              input.mergeLocalizedRerootRule3PriorityChildren sorted }

  /-- Pointwise independent derivations for every exact reroot child. -/
  inductive DeclarativeLocalizedRerootRecursiveRule3SpatialKeyList
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
      Nat → List (input.LocalizedRerootCursor carrierFuel) →
        List input.LocalizedRerootRecursiveRule3SpatialKey → Prop
    | nil (fuel : Nat) :
        input.DeclarativeLocalizedRerootRecursiveRule3SpatialKeyList fuel [] []
    | cons {fuel cursor cursors key keys}
        (head : input.DeclarativeLocalizedRerootRecursiveRule3SpatialKey
          fuel cursor key)
        (tail : input.DeclarativeLocalizedRerootRecursiveRule3SpatialKeyList
          fuel cursors keys) :
        input.DeclarativeLocalizedRerootRecursiveRule3SpatialKeyList
          fuel (cursor :: cursors) (key :: keys)
end

private theorem mapM_buildLocalizedRerootRecursiveRule3SpatialKey?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (sound : ∀ (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootRecursiveRule3SpatialKey),
      input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel cursor = some key →
      input.DeclarativeLocalizedRerootRecursiveRule3SpatialKey fuel cursor key) :
    ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel))
      (keys : List input.LocalizedRerootRecursiveRule3SpatialKey),
      cursors.mapM (input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel) = some keys →
      input.DeclarativeLocalizedRerootRecursiveRule3SpatialKeyList fuel cursors keys
  | [], keys, computed => by
      simp at computed
      subst keys
      exact DeclarativeLocalizedRerootRecursiveRule3SpatialKeyList.nil fuel
  | cursor :: cursors, keys, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : input.buildLocalizedRerootRecursiveRule3SpatialKey?
          fuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              exact DeclarativeLocalizedRerootRecursiveRule3SpatialKeyList.cons
                (sound cursor head headComputed)
                (input.mapM_buildLocalizedRerootRecursiveRule3SpatialKey?_sound
                  sound cursors tail tailComputed)

/-- Successful compilation covers the exact reroot frame, every resolved local observation,
every recursive child, and a descending permutation at every parent. -/
theorem buildLocalizedRerootRecursiveRule3SpatialKey?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootRecursiveRule3SpatialKey),
      input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel cursor = some key →
      input.DeclarativeLocalizedRerootRecursiveRule3SpatialKey fuel cursor key
  | 0, cursor, key, computed => by
      unfold buildLocalizedRerootRecursiveRule3SpatialKey? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          cases observationComputed :
              input.localizedRule3SpatialNode? cursor.occurrence.1.node with
          | none => simp [childrenComputed, observationComputed] at computed
          | some observation =>
              by_cases terminal : children = []
              · simp [childrenComputed, observationComputed, terminal] at computed
                subst key
                exact DeclarativeLocalizedRerootRecursiveRule3SpatialKey.terminal
                  (input.localizedRerootChildren?_sound
                    cursor children childrenComputed)
                  terminal
                  (input.localizedRule3SpatialNode?_outcome_sound
                    cursor.occurrence.1.node observation observationComputed)
              · simp [childrenComputed, observationComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildLocalizedRerootRecursiveRule3SpatialKey? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          cases observationComputed :
              input.localizedRule3SpatialNode? cursor.occurrence.1.node with
          | none => simp [childrenComputed, observationComputed] at computed
          | some observation =>
              by_cases terminal : children = []
              · simp [childrenComputed, observationComputed, terminal] at computed
                subst key
                exact DeclarativeLocalizedRerootRecursiveRule3SpatialKey.terminal
                  (input.localizedRerootChildren?_sound
                    cursor children childrenComputed)
                  terminal
                  (input.localizedRule3SpatialNode?_outcome_sound
                    cursor.occurrence.1.node observation observationComputed)
              · cases childKeysComputed : children.mapM
                    (input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel) with
                | none =>
                    simp [childrenComputed, observationComputed, terminal,
                      childKeysComputed] at computed
                | some childKeys =>
                    simp [childrenComputed, observationComputed, terminal,
                      childKeysComputed] at computed
                    subst key
                    exact DeclarativeLocalizedRerootRecursiveRule3SpatialKey.branch
                      (input.localizedRerootChildren?_sound
                        cursor children childrenComputed)
                      terminal
                      (input.localizedRule3SpatialNode?_outcome_sound
                        cursor.occurrence.1.node observation observationComputed)
                      (input.mapM_buildLocalizedRerootRecursiveRule3SpatialKey?_sound
                        (fun child childKey childComputed =>
                          input.buildLocalizedRerootRecursiveRule3SpatialKey?_sound
                            fuel child childKey childComputed)
                        children childKeys childKeysComputed)
                      (input.sortLocalizedRerootRecursiveRule3SpatialKeys_perm childKeys)
                      (input.sortLocalizedRerootRecursiveRule3SpatialKeys_descending childKeys)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
