import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey
import TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedKey
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Singleton joint reference contexts have exactly the existing scalar promoted semantics.
This is a representation theorem for every cursor, dependency view and fuel, including failure.
It permits the accepted sparse scalar comparator to execute actual singleton joint comparisons.
No generated labels, comparator outcomes or chemical-policy equivalences are assumed. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSingleton

open CertifiedLocalizedCIPInput DeclarativeCIP.PromotedCanonical
open LocalizedMarkedRetainedPromotedKey LocalizedChemicalRingJointMarkerKey
open LocalizedMarkedRetainedSparsePromotedKey

variable (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}

def singletonKey (key : PromotedKey input) : JointPromotedKey input :=
  ⟨key.prior, [key.marker]⟩

theorem compare_singletonKey (left right : PromotedKey input) :
    compareJointKeys input (singletonKey input left) (singletonKey input right) =
      compareKeys input left right := by
  unfold compareJointKeys compareKeys singletonKey
  have singleton : compare [left.marker] [right.marker] = compare left.marker right.marker := by
    rw [List.compare_cons_cons]
    simp
  rw [singleton]

theorem sort_singletonKey (keys : List (PromotedKey input)) :
    sortJointKeys input (keys.map (singletonKey input)) =
      (sortKeys input keys).map (singletonKey input) :=
  (List.map_insertionSort (fun a b => compareKeys input a b ≠ .lt)
    (fun a b => compareJointKeys input a b ≠ .lt) (singletonKey input) keys
    fun a _ b _ => by dsimp only; rw [compare_singletonKey]).symm

theorem assemble_singleton (W D : Nat) (mark : Nat) (children : List MarkerKey) :
    assembleJointMarker W D 1 [mark] (children.map fun key => [key]) =
      [assembleMarker W D mark children] := by
  simp [assembleJointMarker, List.map_map, Function.comp_def]

theorem jointMarkers_singleton (reference : input.Atom) (W D : Nat)
    (keys : List (PromotedKey input)) (cursor : input.LocalizedRerootCursor carrierFuel) :
    jointMarkers input [reference] W D (keys.map (singletonKey input)) cursor =
      [assembleMarker W D (referenceBit input reference cursor)
        (keys.map PromotedKey.marker)] := by
  unfold jointMarkers referenceVector
  simp only [List.length_singleton, List.map_cons, List.map_nil, List.map_map]
  have children : keys.map (JointPromotedKey.markers ∘ singletonKey input) =
      (keys.map PromotedKey.marker).map (fun key => [key]) := by
    rw [List.map_map]
    rfl
  rw [children, assemble_singleton]

private theorem mapM_option_map {α β γ : Type} (h : α → Option β) (s : β → γ) :
    ∀ l : List α, l.mapM (fun p => (h p).map s) = (l.mapM h).map (List.map s)
  | [] => rfl
  | a :: l => by
      simp only [List.mapM_cons, mapM_option_map h s l]
      cases h a <;> cases l.mapM h <;> rfl

section Builder
variable (target : input.LocalizedCIPOccurrence carrierFuel)
  (view : input.LocalizedDependencyView target) (reference : input.Atom) (W D : Nat)

theorem buildJoint_singleton : ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
    buildJoint? input target view [reference] W D fuel cursor =
      (build? input target view reference W D fuel cursor).map (singletonKey input)
  | 0, cursor => by
      cases hp : ordinaryKey? input target view cursor with
      | none => simp [buildJoint?, build?, hp]
      | some prior =>
        cases hc : input.executableLocalizedRerootChildren? cursor with
        | none => simp [buildJoint?, build?, hp, hc]
        | some children =>
          by_cases empty : children = []
          · subst empty
            have leaf := jointMarkers_singleton input reference W D [] cursor
            simp only [List.map_nil] at leaf
            simp [buildJoint?, build?, hp, hc, leaf, singletonKey]
          · simp [buildJoint?, build?, hp, hc, empty]
  | fuel + 1, cursor => by
      cases hp : ordinaryKey? input target view cursor with
      | none => simp [buildJoint?, build?, hp]
      | some prior =>
        cases hc : input.executableLocalizedRerootChildren? cursor with
        | none => simp [buildJoint?, build?, hp, hc]
        | some children =>
          have children_eq : children.mapM (buildJoint? input target view [reference] W D fuel) =
              (children.mapM (build? input target view reference W D fuel)).map
                (List.map (singletonKey input)) := by
            rw [← mapM_option_map]
            congr 1
            funext child
            exact buildJoint_singleton fuel child
          cases hk : children.mapM (build? input target view reference W D fuel) with
          | none =>
            rw [hk] at children_eq
            simp [buildJoint?, build?, hp, hc, hk, children_eq]
          | some keys =>
            rw [hk] at children_eq
            simp only [buildJoint?, build?, hp, hc, hk, children_eq, Option.bind_eq_bind,
              Option.bind_some, Option.map_some, sort_singletonKey, jointMarkers_singleton]
            rfl

theorem compareJoint_singleton (left right : input.LocalizedRerootCursor carrierFuel) :
    compareJointAt? input target view [reference] W D left right =
      compareAt? input target view reference W D left right := by
  unfold compareJointAt? compareAt?
  rw [buildJoint_singleton, buildJoint_singleton]
  cases build? input target view reference W D (2 * (carrierFuel + 1)) left with
  | none => rfl
  | some l =>
    cases build? input target view reference W D (2 * (carrierFuel + 1)) right with
    | none => rfl
    | some r =>
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, compare_singletonKey]

theorem compareJoint_singleton_eq_sparse (left right : input.LocalizedRerootCursor carrierFuel) :
    compareJointAt? input target view [reference] W D left right =
      sparseCompareAt? input target view reference W D left right := by
  rw [compareJoint_singleton, sparseCompareAt?_eq]

end Builder
end TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSingleton

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSingleton.singletonKey
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSingleton.compare_singletonKey
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSingleton.sort_singletonKey
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSingleton.assemble_singleton
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSingleton.jointMarkers_singleton
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSingleton.buildJoint_singleton
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSingleton.compareJoint_singleton
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSingleton.compareJoint_singleton_eq_sparse
