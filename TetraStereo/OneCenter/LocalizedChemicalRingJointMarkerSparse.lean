import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey
import TetraStereo.OneCenter.LocalizedPhysicalMarkedSparseMarker
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Executable sparse columns for the whole ordered joint reference vector. Children are sorted
once by the same prior and whole vector. The exact dense-builder equality includes failure and
derives column shape from actual successful builds. No column is canonicalized independently. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSparse

open CertifiedLocalizedCIPInput DeclarativeCIP.PromotedCanonical
open LocalizedChemicalRingJointMarkerKey
open LocalizedMarkedRetainedPromotedKey (ordinaryKey? referenceBit)
open LocalizedPhysicalMarkedSparseMarker (SparseMarker encode assemble compareMarker
  assemble_eq_encode compareMarker_encode_shaped)

variable (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}

structure SparseKey where
  prior : input.LocalizedRerootCompoundRule45Key
  markers : List SparseMarker

def toSparse (key : JointPromotedKey input) : SparseKey input :=
  ⟨key.prior, key.markers.map encode⟩

def compareSparse (left right : SparseKey input) : Ordering :=
  (input.compareLocalizedRerootCompoundThroughRule5 left.prior right.prior).ordering.then
    (List.compareLex compareMarker left.markers right.markers)

def sortSparse (keys : List (SparseKey input)) : List (SparseKey input) :=
  keys.insertionSort fun a b => compareSparse input a b ≠ .lt

def sparseMarkers (references : List input.Atom) (W D : Nat)
    (children : List (SparseKey input)) (cursor : input.LocalizedRerootCursor carrierFuel) :
    List SparseMarker :=
  (List.range references.length).map fun index =>
    assemble W D ((references.map fun reference => referenceBit input reference cursor).getD index 0)
      (children.map fun key => key.markers.getD index [])

def sparseBuild? (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (references : List input.Atom) (W D : Nat) :
    Nat → input.LocalizedRerootCursor carrierFuel → Option (SparseKey input)
  | 0, cursor => do
      let prior ← ordinaryKey? input target view cursor
      let children ← input.executableLocalizedRerootChildren? cursor
      if children = [] then some ⟨prior, sparseMarkers input references W D [] cursor⟩ else none
  | fuel + 1, cursor => do
      let prior ← ordinaryKey? input target view cursor
      let children ← input.executableLocalizedRerootChildren? cursor
      let keys ← children.mapM (sparseBuild? target view references W D fuel)
      some ⟨prior, sparseMarkers input references W D (sortSparse input keys) cursor⟩

def sparseCompareAt? (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (references : List input.Atom) (W D : Nat)
    (left right : input.LocalizedRerootCursor carrierFuel) : Option Ordering := do
  let l ← sparseBuild? input target view references W D (2 * (carrierFuel + 1)) left
  let r ← sparseBuild? input target view references W D (2 * (carrierFuel + 1)) right
  some (compareSparse input l r)

theorem compare_encoded {W D : Nat} (left right : List MarkerKey)
    (leftShape : ∀ column ∈ left, MarkerWellShaped W D column)
    (rightShape : ∀ column ∈ right, MarkerWellShaped W D column) :
    List.compareLex compareMarker (left.map encode) (right.map encode) = compare left right := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons a rest ih =>
    cases right with
    | nil => rfl
    | cons b tail =>
      simp only [List.map_cons]
      rw [List.compareLex_cons_cons, compareMarker_encode_shaped a b
        (leftShape a (by simp)) (rightShape b (by simp)),
        ih tail (fun column member => leftShape column (by simp [member]))
          (fun column member => rightShape column (by simp [member]))]
      exact List.compare_cons_cons.symm

theorem compareSparse_toSparse {W D : Nat} (left right : JointPromotedKey input)
    (leftShape : ∀ column ∈ left.markers, MarkerWellShaped W D column)
    (rightShape : ∀ column ∈ right.markers, MarkerWellShaped W D column) :
    compareSparse input (toSparse input left) (toSparse input right) =
      compareJointKeys input left right := by
  unfold compareSparse compareJointKeys toSparse
  rw [compare_encoded left.markers right.markers leftShape rightShape]

private theorem mapM_option_map {α β γ : Type} (h : α → Option β) (s : β → γ) :
    ∀ l : List α, l.mapM (fun p => (h p).map s) = (l.mapM h).map (List.map s)
  | [] => rfl
  | a :: l => by
      simp only [List.mapM_cons, mapM_option_map h s l]
      cases h a <;> cases l.mapM h <;> rfl

private theorem mapM_mem {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = some y
  | [], ys, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, rest, hrest, rfl⟩ := h
    intro z member
    rcases List.mem_cons.mp member with rfl | tail
    · exact ⟨x, List.mem_cons_self, hy⟩
    · obtain ⟨w, member, hw⟩ := mapM_mem f xs rest hrest z tail
      exact ⟨w, List.mem_cons_of_mem _ member, hw⟩

theorem jointMarkers_shape (references : List input.Atom) (W D : Nat)
    (children : List (JointPromotedKey input)) (cursor : input.LocalizedRerootCursor carrierFuel)
    (shaped : ∀ key ∈ children, ∀ index, index < references.length →
      MarkerWellShaped W D (key.markers.getD index [])) :
    (jointMarkers input references W D children cursor).length = references.length ∧
    ∀ index, index < references.length → MarkerWellShaped W D
      ((jointMarkers input references W D children cursor).getD index []) := by
  constructor
  · simp [jointMarkers, assembleJointMarker]
  · intro index bound
    unfold jointMarkers
    rw [assembleJointMarker_getD W D references.length _ _ bound]
    apply assembleMarker_wellShaped
    intro column member
    obtain ⟨columns, columnsMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨key, keyMember, rfl⟩ := List.mem_map.mp columnsMember
    exact shaped key keyMember index bound

theorem sparseMarkers_eq (references : List input.Atom) (W D : Nat)
    (children : List (JointPromotedKey input)) (cursor : input.LocalizedRerootCursor carrierFuel)
    (shaped : ∀ key ∈ children, ∀ index, index < references.length →
      MarkerWellShaped W D (key.markers.getD index [])) :
    sparseMarkers input references W D (children.map (toSparse input)) cursor =
      (jointMarkers input references W D children cursor).map encode := by
  unfold sparseMarkers jointMarkers assembleJointMarker referenceVector
  simp only [List.map_map]
  apply List.map_congr_left
  intro index member
  have bound := List.mem_range.mp member
  have columns : children.map (fun key => (toSparse input key).markers.getD index []) =
      (children.map fun key => key.markers.getD index []).map encode := by
    rw [List.map_map]
    apply List.map_congr_left
    intro key _
    exact List.getD_map key.markers [] encode
  simp only [Function.comp_def]
  rw [columns]
  exact assemble_eq_encode W D _ _ (by
    intro column present
    obtain ⟨key, member, rfl⟩ := List.mem_map.mp present
    exact shaped key member index bound)

section Builder
variable (target : input.LocalizedCIPOccurrence carrierFuel)
  (view : input.LocalizedDependencyView target) (references : List input.Atom) (W D : Nat)

theorem buildJoint_shape : ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : JointPromotedKey input), buildJoint? input target view references W D fuel cursor = some key →
      key.markers.length = references.length ∧
      ∀ index, index < references.length → MarkerWellShaped W D (key.markers.getD index [])
  | 0, cursor, key, built => by
    simp only [buildJoint?, Option.bind_eq_bind, Option.bind_eq_some_iff] at built
    obtain ⟨prior, _, children, _, rest⟩ := built
    split at rest
    · cases Option.some.inj rest
      exact jointMarkers_shape input references W D [] cursor (by simp)
    · cases rest
  | fuel + 1, cursor, key, built => by
    simp only [buildJoint?, Option.bind_eq_bind, Option.bind_eq_some_iff] at built
    obtain ⟨prior, _, children, _, keys, hkeys, same⟩ := built
    cases Option.some.inj same
    apply jointMarkers_shape
    intro key member index bound
    have original := (List.perm_insertionSort _ keys).mem_iff.mp member
    obtain ⟨child, _, childBuilt⟩ := mapM_mem _ children keys hkeys key original
    exact (buildJoint_shape fuel child key childBuilt).2 index bound

theorem buildJoint_columns (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : JointPromotedKey input) (built : buildJoint? input target view references W D fuel cursor = some key) :
    ∀ column ∈ key.markers, MarkerWellShaped W D column := by
  obtain ⟨length, shape⟩ := buildJoint_shape input target view references W D fuel cursor key built
  intro column member
  obtain ⟨index, bound, equal⟩ := List.getElem_of_mem member
  have shaped := shape index (by omega)
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound, equal] using shaped

theorem sparseBuild?_eq : ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
    sparseBuild? input target view references W D fuel cursor =
      (buildJoint? input target view references W D fuel cursor).map (toSparse input)
  | 0, cursor => by
    cases hp : ordinaryKey? input target view cursor with
    | none => simp [sparseBuild?, buildJoint?, hp]
    | some prior =>
      cases hc : input.executableLocalizedRerootChildren? cursor with
      | none => simp [sparseBuild?, buildJoint?, hp, hc]
      | some children =>
        by_cases empty : children = []
        · subst empty
          have leaf := sparseMarkers_eq input references W D [] cursor (by simp)
          simp only [List.map_nil] at leaf
          simp [sparseBuild?, buildJoint?, hp, hc, toSparse, leaf]
        · simp [sparseBuild?, buildJoint?, hp, hc, empty]
  | fuel + 1, cursor => by
    cases hp : ordinaryKey? input target view cursor with
    | none => simp [sparseBuild?, buildJoint?, hp]
    | some prior =>
      cases hc : input.executableLocalizedRerootChildren? cursor with
      | none => simp [sparseBuild?, buildJoint?, hp, hc]
      | some children =>
        have children_eq : children.mapM (sparseBuild? input target view references W D fuel) =
            (children.mapM (buildJoint? input target view references W D fuel)).map
              (List.map (toSparse input)) := by
          rw [← mapM_option_map]
          congr 1
          funext child
          exact sparseBuild?_eq fuel child
        cases hk : children.mapM (buildJoint? input target view references W D fuel) with
        | none =>
          rw [hk] at children_eq
          simp [sparseBuild?, buildJoint?, hp, hc, hk, children_eq]
        | some keys =>
          rw [hk] at children_eq
          have shaped : ∀ key ∈ keys, ∀ column ∈ key.markers, MarkerWellShaped W D column := by
            intro key member
            obtain ⟨child, _, built⟩ := mapM_mem _ children keys hk key member
            exact buildJoint_columns input target view references W D fuel child key built
          have sorted : sortSparse input (keys.map (toSparse input)) =
              (sortJointKeys input keys).map (toSparse input) :=
            (List.map_insertionSort (fun a b => compareJointKeys input a b ≠ .lt)
              (fun a b => compareSparse input a b ≠ .lt) (toSparse input) keys
              fun a ha b hb => by
                dsimp only
                rw [compareSparse_toSparse input a b (shaped a ha) (shaped b hb)]).symm
          have assembled := sparseMarkers_eq input references W D (sortJointKeys input keys) cursor (by
            intro key member index bound
            have original := (List.perm_insertionSort _ keys).mem_iff.mp member
            obtain ⟨child, _, built⟩ := mapM_mem _ children keys hk key original
            exact (buildJoint_shape input target view references W D fuel child key built).2 index bound)
          simp only [sparseBuild?, buildJoint?, hp, hc, hk, children_eq, Option.bind_eq_bind,
            Option.bind_some, Option.map_some, sorted, assembled]
          rfl

theorem sparseCompareAt?_eq (left right : input.LocalizedRerootCursor carrierFuel) :
    sparseCompareAt? input target view references W D left right =
      compareJointAt? input target view references W D left right := by
  unfold sparseCompareAt? compareJointAt?
  rw [sparseBuild?_eq, sparseBuild?_eq]
  cases hl : buildJoint? input target view references W D (2 * (carrierFuel + 1)) left with
  | none => rfl
  | some l =>
    cases hr : buildJoint? input target view references W D (2 * (carrierFuel + 1)) right with
    | none => rfl
    | some r =>
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
      rw [compareSparse_toSparse input l r
        (buildJoint_columns input target view references W D _ _ l hl)
        (buildJoint_columns input target view references W D _ _ r hr)]

end Builder
end TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSparse

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSparse.toSparse
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSparse.compareSparse
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSparse.sortSparse
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSparse.sparseMarkers
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSparse.sparseBuild?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSparse.sparseCompareAt?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSparse.compare_encoded
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSparse.compareSparse_toSparse
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSparse.jointMarkers_shape
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSparse.sparseMarkers_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSparse.buildJoint_shape
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSparse.buildJoint_columns
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSparse.sparseBuild?_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSparse.sparseCompareAt?_eq
