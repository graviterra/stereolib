import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier
import TetraStereo.OneCenter.LocalizedChemicalRingRootSliceCache
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootSlice

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier

private theorem filter_dedup {α : Type} [DecidableEq α] (p : α → Bool) (xs : List α) :
    xs.dedup.filter p = (xs.filter p).dedup := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      cases hp : p a <;> by_cases hm : a ∈ xs <;>
        simp [hp, hm, ih]

private theorem flatMap_filter {α β : Type} (p : α → Bool) (f : α → List β) (xs : List α) :
    (xs.filter p).flatMap f = xs.flatMap (fun a => if p a then f a else []) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases hp : p a <;> simp [hp, ih]

def rootFrames : List input.LocalizedCIPOccurrenceFrame :=
  (subtree (0 : Fin 25) 27 [] (OfficialCIPNode.root (0 : Fin 25))).dedup

private theorem filter_root (root : Fin 25) :
    (input.localizedOccurrencesAtAtom 26 root).filter (fun frame => frame.root == (0 : Fin 25)) =
      if root == (0 : Fin 25) then input.localizedOccurrencesAtAtom 26 root else [] := by
  have tag (frame : input.LocalizedCIPOccurrenceFrame)
      (member : frame ∈ input.localizedOccurrencesAtAtom 26 root) : frame.root = root :=
    input.declarativeLocalizedOccurrenceSubtree_root_eq
      ((input.mem_localizedOccurrencesAtAtom_iff 26 root frame).mp member)
  by_cases same : root = (0 : Fin 25)
  · subst root
    simp only [beq_self_eq_true, if_true]
    apply List.filter_eq_self.mpr
    intro frame member
    exact beq_iff_eq.mpr (tag frame member)
  · simp only [beq_iff_eq, same, if_false]
    apply List.filter_eq_nil_iff.mpr
    intro frame member observed
    exact same ((tag frame member).symm.trans (beq_iff_eq.mp observed))

theorem rootFrames_eq : rootFrames =
    (input.localizedOccurrences 26).filter (fun frame => frame.root == (0 : Fin 25)) := by
  have roots : (List.finRange 25).filter (fun root => root == (0 : Fin 25)) = [0] := by
    decide +kernel
  calc
    rootFrames = ((List.finRange 25).filter (fun root => root == (0 : Fin 25)) |>.flatMap
        (input.localizedOccurrencesAtAtom 26)).dedup := by
      rw [roots]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      unfold rootFrames localizedOccurrencesAtAtom
      rw [subtree_eq]
    _ = (((List.finRange 25).flatMap (input.localizedOccurrencesAtAtom 26)).filter
        (fun frame => frame.root == (0 : Fin 25))).dedup := by
      congr 1
      rw [flatMap_filter, List.filter_flatMap]
      apply LocalizedGenericMarkedRecalculation.flatMap_congr_mem
      intro root _
      exact (filter_root root).symm
    _ = (input.localizedOccurrences 26).filter (fun frame => frame.root == (0 : Fin 25)) := by
      exact (filter_dedup (fun frame : input.LocalizedCIPOccurrenceFrame => frame.root == (0 : Fin 25))
        ((List.finRange 25).flatMap (input.localizedOccurrencesAtAtom 26))).symm

private noncomputable def proofSlice : input.LocalizedRerootRootSliceCache 26 :=
  { full := input.localizedRerootCarrierCache 26
    root := (0 : Fin 25)
    frames := rootFrames
    correct := rootFrames_eq }

def rootNeighbors (frame : input.LocalizedCIPOccurrenceFrame) : List input.LocalizedCIPOccurrenceFrame :=
  (rootFrames.filter fun candidate => candidate.root == frame.root &&
    candidate.address.length + 1 == frame.address.length && candidate.address == frame.address.dropLast) ++
  (rootFrames.filter fun candidate => candidate.root == frame.root &&
    candidate.address.length == frame.address.length + 1 && candidate.address.dropLast == frame.address)

private theorem rootNeighbors_eq (frame : input.LocalizedCIPOccurrenceFrame)
    (atRoot : frame.root = (0 : Fin 25)) :
    rootNeighbors frame = input.localizedRerootNeighborFrames (fuel := 26) frame := by
  calc
    rootNeighbors frame = proofSlice.neighborFrames frame := by
      simp only [rootNeighbors, LocalizedRerootRootSliceCache.neighborFrames, proofSlice, atRoot, if_true]
    _ = proofSlice.full.neighborFrames frame := proofSlice.neighborFrames_eq frame
    _ = input.localizedRerootNeighborFrames (fuel := 26) frame := by
      rfl

def rootIntended (cursor : input.LocalizedRerootCursor 26) : List input.LocalizedCIPOccurrenceFrame :=
  if cursor.occurrence.1.node.isDuplicateLeaf then [] else
    match cursor.previous? with
    | none => rootNeighbors cursor.occurrence.1
    | some previous => (rootNeighbors cursor.occurrence.1).filter fun frame =>
        frame.address != previous.1.address

private theorem rootIntended_eq (cursor : input.LocalizedRerootCursor 26)
    (atRoot : cursor.occurrence.1.root = (0 : Fin 25)) :
    rootIntended cursor = input.intendedLocalizedRerootChildFrames cursor := by
  cases leaf : cursor.occurrence.1.node.isDuplicateLeaf <;>
    cases previous : cursor.previous? <;>
    simp only [rootIntended, intendedLocalizedRerootChildFrames, leaf, previous,
      Bool.false_eq_true, if_false, if_true, rootNeighbors_eq cursor.occurrence.1 atRoot]

def readChildren (cursor : input.LocalizedRerootCursor 26) :
    Option (List (input.LocalizedRerootCursor 26)) :=
  if atRoot : cursor.occurrence.1.root = (0 : Fin 25) then
    some ((rootIntended cursor).attach.map fun frame =>
      { occurrence := ⟨frame.1,
          input.mem_localizedOccurrences_of_mem_intendedLocalizedRerootChildFrames cursor frame.1
            (by rw [← rootIntended_eq cursor atRoot]; exact frame.2)⟩
        previous? := some cursor.occurrence })
  else input.executableLocalizedRerootChildren? cursor

private theorem map_attach_congr {α β : Type} (xs ys : List α) (same : xs = ys)
    (f : {x // x ∈ xs} → β) (g : {x // x ∈ ys} → β)
    (pointwise : ∀ x hx hy, f ⟨x, hx⟩ = g ⟨x, hy⟩) : xs.attach.map f = ys.attach.map g := by
  subst ys
  apply List.map_congr_left
  intro entry _
  exact pointwise entry.1 entry.2 entry.2

theorem readChildren_eq (cursor : input.LocalizedRerootCursor 26) :
    readChildren cursor = input.executableLocalizedRerootChildren? cursor := by
  unfold readChildren
  split
  · rename_i atRoot
    unfold executableLocalizedRerootChildren? executableLocalizedRerootChildren
    congr 1
    apply map_attach_congr _ _ (rootIntended_eq cursor atRoot)
    intros
    rfl
  · rfl

def reader : input.LocalizedRerootChildReader 26 := ⟨readChildren, readChildren_eq⟩

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootSlice

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootSlice.rootFrames_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootSlice.readChildren_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootSlice.reader
