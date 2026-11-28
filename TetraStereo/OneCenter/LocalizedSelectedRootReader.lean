import TetraStereo.OneCenter.LocalizedChemicalRingRootSliceCache

/-! Generate the occurrence carrier of one selected atom directly. Every
child read retains the original addresses, order, and incoming cut. -/
set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput.SelectedRoot
open private filter_root_redundant map_attach_congr from TetraStereo.OneCenter.LocalizedChemicalRingRootSliceCache

variable (i : CertifiedLocalizedCIPInput) (fuel : Nat)

def frames (a : i.Atom) := (i.localizedOccurrencesAtAtom fuel a).dedup

private theorem filter_dedup {α : Type} [DecidableEq α] (p : α → Bool) (xs : List α) :
    xs.dedup.filter p = (xs.filter p).dedup := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases hp : p a <;> by_cases hm : a ∈ xs <;> simp [hp,hm,ih]

theorem frames_eq (a : i.Atom) :
    frames i fuel a = (i.localizedOccurrences fuel).filter (fun f => f.root == a) := by
  unfold frames localizedOccurrences
  rw [filter_dedup,List.filter_flatMap]
  apply congrArg List.dedup
  let roots := List.finRange i.certified.input.molecule.atomCount
  have only : roots.filter (· == a) = [a] := by
    apply List.perm_singleton.mp
    apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).filter _) (by simp)).mpr
    intro b
    simp
  conv_lhs => rw [show i.localizedOccurrencesAtAtom fuel a =
      ([a].flatMap (i.localizedOccurrencesAtAtom fuel)) by simp, ← only]
  change (roots.filter (· == a)).flatMap _ = roots.flatMap _
  induction roots with
  | nil => rfl
  | cons b bs ih =>
    have tag (f) (h : f ∈ i.localizedOccurrencesAtAtom fuel b) : f.root = b :=
      i.declarativeLocalizedOccurrenceSubtree_root_eq ((i.mem_localizedOccurrencesAtAtom_iff _ _ _).mp h)
    by_cases h : b = a
    · subst b
      have all := List.filter_eq_self.mpr (fun f hf => beq_iff_eq.mpr (tag f hf))
      simp [ih,all]
    · have empty : (i.localizedOccurrencesAtAtom fuel b).filter (fun f => f.root == a) = [] :=
        List.filter_eq_nil_iff.mpr (fun f hf hit => h ((tag f hf).symm.trans (beq_iff_eq.mp hit)))
      simp [h,ih,empty]

private def neighbors (fs : List i.LocalizedCIPOccurrenceFrame) (f : i.LocalizedCIPOccurrenceFrame) :=
  (fs.filter fun c => c.root == f.root && c.address.length + 1 == f.address.length &&
    c.address == f.address.dropLast) ++
  (fs.filter fun c => c.root == f.root && c.address.length == f.address.length + 1 &&
    c.address.dropLast == f.address)

private theorem neighbors_eq (f : i.LocalizedCIPOccurrenceFrame) :
    neighbors i (frames i fuel f.root) f = i.localizedRerootNeighborFrames (fuel := fuel) f := by
  rw [frames_eq]
  unfold neighbors localizedRerootNeighborFrames localizedCarrierParentFrames localizedCarrierOutwardChildFrames
  congr 1 <;> apply filter_root_redundant <;> intro c h <;>
    simp only [Bool.and_eq_true,beq_iff_eq] at h <;> exact h.1.1

private def intended (a : i.Atom) (fs : List i.LocalizedCIPOccurrenceFrame) (q : i.LocalizedRerootCursor fuel) :=
  if q.occurrence.val.root = a then
    if q.occurrence.val.node.isDuplicateLeaf then []
    else match q.previous? with
      | none => neighbors i fs q.occurrence.val
      | some prev => (neighbors i fs q.occurrence.val).filter (fun f => f.address != prev.val.address)
  else i.intendedLocalizedRerootChildFrames q

private theorem intended_eq (a : i.Atom) (q : i.LocalizedRerootCursor fuel) :
    intended i fuel a (frames i fuel a) q = i.intendedLocalizedRerootChildFrames q := by
  unfold intended
  split
  · rename_i same
    rw [← same,neighbors_eq]
    rfl
  · rfl

/-- The carrier for the selected root is shared by all reads. Requests for
another root still have the total executable semantics. -/
def reader (a : i.Atom) : i.LocalizedRerootChildReader fuel :=
  let fs := frames i fuel a
  let read (q : i.LocalizedRerootCursor fuel) : Option (List (i.LocalizedRerootCursor fuel)) :=
    some ((intended i fuel a fs q).attach.map fun f =>
      ⟨⟨f.val,i.mem_localizedOccurrences_of_mem_intendedLocalizedRerootChildFrames q f.val
        ((intended_eq i fuel a q) ▸ f.property)⟩,some q.occurrence⟩)
  ⟨read,by
    intro q
    unfold read executableLocalizedRerootChildren? executableLocalizedRerootChildren
    congr 1
    apply map_attach_congr _ _ (intended_eq i fuel a q)
    intros
    rfl⟩

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput.SelectedRoot

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.SelectedRoot.frames_eq
